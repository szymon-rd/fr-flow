package frflow.proof.lean.lower

import cats.data.Writer
import cats.syntax.all.*
import frflow.core.analysis.Fixed
import frflow.core.expr.{Expr, Value}
import frflow.core.name.{DefName, NodeId, SymbolName, TypeName}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.obligation.{Evaluated, Evaluation, Hyp, Prop, Substitute}
import frflow.proof.terms.{FixedAs, OpenTerms, TermTable}

/** A proposition as a Lean statement: each declaration applied to its open terms, each term replaced by its
  * definition in force or its substitute; the open terms left are bound by `Forall` (or `Exists`) in the order met
  * (the claims it is about, the conclusion, the hypotheses), then the hypotheses `h_<Node>`. Today's
  * `Refinement.claim`, `stated` and `Vocabulary.term`, on values.
  */
final class LowerProp(table: TermTable, env: LowerEnv):
  import Atoms.{call, name}
  private type W[A] = Writer[OpenTerms, A]
  private type Subst = Map[SymbolName, Substitute]

  def statement(p: Prop): LExpr = p match
    case Prop.Forall(about, body) => closed(about, body)(LExpr.Forall(_, _))
    case Prop.Exists(about, body) => closed(about, body)(LExpr.Exists(_, _))
    case other                   => prop(other, Map.empty).value

  private def closed(about: List[NodeId], body: Prop)(q: (List[LBinder], LExpr) => LExpr): LExpr =
    val (opens, b) = (about.traverse(n => prop(Prop.claim(n), Map.empty)) *> withHyps(body)).run
    binders(opens) match
      case Nil => b
      case bs  => q(bs, b)

  /** `∀ (h_A : …) (h_B : …), c` for an implication at the top of a statement. */
  private def withHyps(p: Prop): W[LExpr] = p match
    case Prop.Implies(Nil, c) => prop(c, Map.empty)
    case Prop.Implies(hs, c)  => (prop(c, Map.empty), hs.traverse(hyp)).mapN((x, bs) => LExpr.Forall(bs, x))
    case other                => prop(other, Map.empty)

  private def hyp(h: Hyp): W[LBinder] = prop(h.prop, Map.empty).map(LBinder.Explicit(Names.builtin(h.name), _))

  def prop(p: Prop, σ: Subst): W[LExpr] = p match
    case Prop.ClaimOf(n, more)   => applied(decl(n, "claim"), table.claims.getOrElse(n, OpenTerms.empty), σ ++ more)
    case Prop.ConjunctOf(n, i)   => applied(decl(n, s"conjunct_$i"), table.claims.getOrElse(n, OpenTerms.empty), σ)
    case Prop.Expected(n, i)     =>
      applied(decl(n, s"expected_$i"), table.expected.getOrElse((n, i), OpenTerms.empty), σ)
    case Prop.Iff(a, b)          => (prop(a, σ), prop(b, σ)).mapN((x, y) => LExpr.Paren(LExpr.Infix(LOp.Iff, x, y)))
    case Prop.Both(ps)           => ps.traverse(prop(_, σ)).map(_.toList.reduceRight(LExpr.Infix(LOp.And, _, _)))
    case Prop.Not(a)             => prop(a, σ).map(LExpr.Prefix(LPrefix.NotSpaced, _))
    case Prop.False              => Writer.value(name("False"))
    case Prop.Implies(hs, c)     => (hs.traverse(h => prop(h.prop, σ)), prop(c, σ)).mapN((xs, y) =>
                                      (xs :+ y).reduceRight(LExpr.Infix(LOp.Arrow, _, _)))
    case Prop.Evaluates(e)       => Writer.value(evaluates(e))
    case Prop.Formula(_) | Prop.Commutes(_, _) | Prop.Forall(_, _) | Prop.Exists(_, _) =>
      ??? // a formula lowered by `Lower` with its open terms told; commutation as today's `commute_i`; nested binders

  /** `f` applied to its open terms: `(Crm.ExpiryJob.claim expire runExpiry)`, or `f` alone over none. */
  private def applied(f: LExpr, terms: OpenTerms, σ: Subst): W[LExpr] =
    (terms.sorts.traverse(sort), terms.symbols.traverse(symbol(_, σ))).mapN(_ ++ _)
      .map(args => if args.isEmpty then f else call(f, args))

  private def sort(t: TypeName): W[LExpr] = table.fixings.get(Fixed.Sort(t)) match
    case Some(FixedAs.Type(ty)) => Writer.value(LowerType(ty))
    case _                      => Writer.tell(OpenTerms(List(t), Nil)).as(LExpr.Name(Names.ident(t.value)))

  private def symbol(s: SymbolName, σ: Subst): W[LExpr] = σ.get(s) match
    case Some(Substitute.Code(d)) => applied(define(d), table.defines.getOrElse(d, OpenTerms.empty), σ)
    case Some(Substitute.Nothing) => Writer.value(nothing(table.typeOf(s)))
    case None                     => table.fixings.get(Fixed.Term(s)) match
      case Some(FixedAs.Term(over)) => applied(LExpr.Const(Names.path(env.kb.value, s.value)), over, σ)
      case _                        => Writer.tell(leaf(s)).as(LExpr.Name(Names.ident(s.value)))

  /** A symbol left open, and the opaque types its type names that no definition fixes. */
  private def leaf(s: SymbolName): OpenTerms =
    val sorts = Ty.parts(table.typeOf(s)).collect { case Ty.Sort(n) => n }.distinct
    OpenTerms(sorts.filterNot(n => table.fixings.contains(Fixed.Sort(n))), List(s))

  /** `fun (x0 : A) (x1 : B) => []`: an operation doing nothing (`Substitute.canDoNothing` holds of its type). */
  private def nothing(t: Ty): LExpr = t match
    case Ty.FnOf(ins, r) =>
      val xs = ins.indices.map(i => Names.builtin(s"x$i")).toList
      LExpr.Paren(LExpr.Fun(xs.zip(ins).map((x, ty) => LBinder.Explicit(x, LowerType(ty))), nothingOf(r, ins, xs)))
    case _ => throw IllegalStateException("FrFlow bug: doing nothing for an operation that is not a function")

  /** `False`, `[]`, `none`, or the first input of the result's type, returned unchanged. */
  private def nothingOf(r: Ty, ins: List[Ty], xs: List[LeanName]): LExpr = r match
    case Ty.Bool        => name("False")
    case Ty.ListOf(_)   => LExpr.ListLit(Nil)
    case Ty.OptionOf(_) => name("none")
    case other          => xs.zip(ins).collectFirst { case (x, `other`) => LExpr.Name(x) }
      .getOrElse(throw IllegalStateException("FrFlow bug: no input to return unchanged"))

  /** `(K.N.post givens…) inputs…`, negated when Scala found it false; `(K.d givens…) inputs… = value` for code. Closed:
    * every open term has a given, every opaque type a definition in force.
    */
  private def evaluates(e: Evaluation): LExpr =
    val lower = Lower(env)
    def closed(x: Expr) = lower.expr(x).runA(Naming.over(Set.empty, Set.empty)).value
    def givenTo(f: LExpr, over: OpenTerms) =
      val (opens, sorts) = over.sorts.traverse(sort).run
      if opens.sorts.nonEmpty then throw IllegalStateException("FrFlow bug: an open type in an evaluation")
      val args = sorts ++ over.symbols.map(s => e.givens.get(s).fold(LExpr.Name(Names.ident(s.value)))(closed))
      LExpr.App(if args.isEmpty then f else call(f, args), e.inputs.map(closed))
    (e.subject, e.value) match
      case (Evaluated.Post(n), Expr.Lit(Value.Bool(holds), _)) =>
        val held = givenTo(decl(n, "post"), table.posts.getOrElse(n, OpenTerms.empty))
        if holds then held else LExpr.Prefix(LPrefix.NotSpaced, LExpr.Paren(held))
      case (Evaluated.Code(d), v) =>
        LExpr.Infix(LOp.Eq, givenTo(define(d), table.defines.getOrElse(d, OpenTerms.empty)), closed(v))
      case (Evaluated.Post(_), _) => throw IllegalStateException("FrFlow bug: a post evaluated to a non-Boolean")

  private def decl(n: NodeId, d: String): LExpr = LExpr.Const(Names.path(env.kb.value, n.value, d))
  private def define(d: DefName): LExpr = LExpr.Const(Names.path(env.kb.value, d.value))

  private def binders(opens: OpenTerms): List[LBinder] =
    Option.when(opens.sorts.nonEmpty)(LBinder.Several(opens.sorts.map(n => Names.ident(n.value)), name("Type")))
      .toList ++ opens.symbols.map(s => LBinder.Explicit(Names.ident(s.value), LowerType.binder(table.typeOf(s))))
