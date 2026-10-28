package frflow.proof.lean.lower

import cats.data.Writer
import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{DefName, NodeId, SymbolName, TypeName}
import frflow.core.spec.{Form, Written}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.obligation.{Constant, Hyp, Prop, Substitute}
import frflow.proof.terms.{OpenTerms, TermTable}

/** A proposition as a Lean statement: each declaration applied to its open terms, each term replaced by its
  * substitute; the open terms left are bound by `Forall` (or `Exists`) in the order met
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
    case Prop.ForEvery(ss, body)  => named(ss, statement(body))(LExpr.Forall(_, _))
    case Prop.ForSome(ss, body)   => named(ss, statement(body))(LExpr.Exists(_, _))
    case other                   => prop(other, Map.empty).value

  /** `∀`/`∃` exactly `ss`, each at its type; nothing to bind, the body alone. */
  private def named(ss: List[SymbolName], body: LExpr)(q: (List[LBinder], LExpr) => LExpr): LExpr =
    if ss.isEmpty then body else q(binders(OpenTerms(Nil, ss)), body)

  private def closed(about: List[NodeId], body: Prop)(q: (List[LBinder], LExpr) => LExpr): LExpr =
    val (opens, b) = (about.traverse(n => prop(Prop.claim(n), Map.empty)) *> withHyps(body)).run
    binders(opens) match
      case Nil => b
      case bs  => q(bs, b)

  /** The open terms a statement binds, in order: what `statement` quantifies over. */
  def opens(p: Prop): OpenTerms = p match
    case Prop.Forall(about, body) => (about.traverse(n => prop(Prop.claim(n), Map.empty)) *> withHyps(body)).run._1
    case Prop.Exists(about, body) => opens(Prop.Forall(about, body))
    case other                    => prop(other, Map.empty).run._1

  /** `∀ (h_A : …) (h_B : …), c` for an implication at the top of a statement. */
  private def withHyps(p: Prop): W[LExpr] = p match
    case Prop.Implies(Nil, c) => prop(c, Map.empty)
    case Prop.Implies(hs, c)  => (prop(c, Map.empty), hs.traverse(hyp)).mapN((x, bs) => LExpr.Forall(bs, x))
    case other                => prop(other, Map.empty)

  private def hyp(h: Hyp): W[LBinder] = prop(h.prop, Map.empty).map(LBinder.Explicit(Names.builtin(h.name), _))

  def prop(p: Prop, σ: Subst): W[LExpr] = p match
    case Prop.ClaimOf(n, more)   => applied(decl(n, "claim"), table.claims.getOrElse(n, OpenTerms.empty), σ ++ more)
    case Prop.Keeps(i, op, f, m) => applied(decl(i, s"keeps_${op.value}"), LowerProp.opens(f), σ ++ m)
    case Prop.Makes(i, op, f, m) => applied(decl(i, s"makes_${op.value}"), LowerProp.opens(f), σ ++ m)
    case Prop.ConjunctOf(n, i)   => applied(decl(n, s"conjunct_$i"), table.claims.getOrElse(n, OpenTerms.empty), σ)
    case Prop.Starts(d, e, i, ty) => Writer.value(starts(d, e, i, ty))
    case Prop.Inhabited(d, ty)   => Writer.value(inhabited(d, ty))
    case Prop.Iff(a, b)          => (prop(a, σ), prop(b, σ)).mapN((x, y) => LExpr.Paren(LExpr.Infix(LOp.Iff, x, y)))
    case Prop.Both(ps)           => ps.traverse(prop(_, σ)).map(_.toList.reduceRight(LExpr.Infix(LOp.And, _, _)))
    case Prop.Not(a)             => prop(a, σ).map(LExpr.Prefix(LPrefix.NotSpaced, _))
    case Prop.False              => Writer.value(name("False"))
    case Prop.Implies(hs, c)     => (hs.traverse(h => prop(h.prop, σ)), prop(c, σ)).mapN((xs, y) =>
                                      (xs :+ y).reduceRight(LExpr.Infix(LOp.Arrow, _, _)))
    case Prop.Formula(w)         => formula(w)
    case Prop.Commutes(c, opens)  => opens.traverse(s => Writer.tell(leaf(s))).as(LowerCommute(env, closedNaming)(c))
    case Prop.Forall(_, _) | Prop.Exists(_, _) => Writer.value(LExpr.Paren(statement(p)))
    case Prop.ForEvery(ss, body) => inner(ss, body, σ)(LExpr.Forall(_, _))
    case Prop.ForSome(ss, body)  => inner(ss, body, σ)(LExpr.Exists(_, _))

  /** A statement inside another binding exactly `ss`: the open terms it leaves are the enclosing statement's. */
  private def inner(ss: List[SymbolName], body: Prop, σ: Subst)(q: (List[LBinder], LExpr) => LExpr): W[LExpr] =
    val (opens, b) = prop(body, σ).run
    val left = OpenTerms((opens.sorts ++ ss.flatMap(leaf(_).sorts)).distinct, opens.symbols.filterNot(ss.contains))
    Writer(left, if ss.isEmpty then b else LExpr.Paren(q(binders(OpenTerms(Nil, ss)), b)))

  /** A formula printed from its term (`Printed`), its open terms told: the symbols its IR (`Written.value`, made once
    * when elaborated) mentions.
    */
  private def formula(w: Written[Expr]): W[LExpr] = w.form match
    case Form.Term(t)  =>
      Writer(OpenTerms(Nil, Exprs.mentions(w.value).symbols), Printed.formula(env, closedNaming)(t.run))
    case Form.Steps(_) => throw IllegalStateException("FrFlow bug: a program's steps as a formula")

  /** `f` applied to its open terms: `(Crm.ExpiryJob.claim expire runExpiry)`, or `f` alone over none. */
  private def applied(f: LExpr, terms: OpenTerms, σ: Subst): W[LExpr] =
    (terms.sorts.traverse(sort), terms.symbols.traverse(symbol(_, σ))).mapN(_ ++ _)
      .map(args => if args.isEmpty then f else call(f, args))

  private def sort(t: TypeName): W[LExpr] = Writer.tell(OpenTerms(List(t), Nil)).as(LExpr.Name(Names.ident(t.value)))

  /** A define applied to its open terms, each a value `known` gives it or its name: proven code inside a witness. */
  def code(d: DefName, known: Map[SymbolName, LExpr]): LExpr =
    val terms = table.defines.getOrElse(d, OpenTerms.empty)
    val args = terms.sorts.map(n => LExpr.Name(Names.ident(n.value))) ++
      terms.symbols.map(s => known.getOrElse(s, LExpr.Name(Names.ident(s.value))))
    if args.isEmpty then define(d) else call(define(d), args)

  /** What a symbol is written as under `σ`: its substitute applied to its own open terms, or its name. */
  def standing(s: SymbolName, σ: Subst): LExpr = symbol(s, σ).value

  private def symbol(s: SymbolName, σ: Subst): W[LExpr] = σ.get(s) match
    case Some(Substitute.Code(d)) => applied(define(d), table.defines.getOrElse(d, OpenTerms.empty), σ)
    case Some(Substitute.Fixed(c)) => Writer.value(constant(c))
    case Some(Substitute.Nothing) => Writer.value(nothing(table.typeOf(s)))
    case None                     => Writer.tell(leaf(s)).as(LExpr.Name(Names.ident(s.value)))

  /** A symbol left open, and the opaque types its type names. */
  private def leaf(s: SymbolName): OpenTerms =
    OpenTerms(Ty.parts(table.typeOf(s)).collect { case Ty.Sort(n) => n }.distinct, List(s))

  /** `fun (x0 : A) (x1 : B) => []`: a Definition doing nothing (`Substitute.canDoNothing` holds of its type). */
  private def nothing(t: Ty): LExpr = t match
    case Ty.FnOf(ins, r) =>
      val xs = ins.indices.map(i => Names.builtin(s"x$i")).toList
      LExpr.Paren(LExpr.Fun(xs.zip(ins).map((x, ty) => LBinder.Explicit(x, LowerType(ty))), nothingOf(r, ins, xs)))
    case _ => throw IllegalStateException("FrFlow bug: doing nothing for a Definition that is not a function")

  /** `False`, `[]`, `none`, or the first input of the result's type, returned unchanged. */
  private def nothingOf(r: Ty, ins: List[Ty], xs: List[LeanName]): LExpr = r match
    case Ty.Bool        => name("False")
    case Ty.ListOf(_)   => LExpr.ListLit(Nil)
    case Ty.OptionOf(_) => name("none")
    case other          => xs.zip(ins).collectFirst { case (x, `other`) => LExpr.Name(x) }
      .getOrElse(throw IllegalStateException("FrFlow bug: no input to return unchanged"))

  /** `(K.rule s)`, or `∀ x ∈ s, (K.rule x)` of each element: an `always` at a store's starting state. */
  /** `∀ (s : S), (K.initially s) → (K.rule s)`, or `→ ∀ x ∈ s, (K.rule x)`. */
  private def starts(d: DefName, each: Boolean, initially: DefName, ty: Ty): LExpr =
    val s = name("s")
    val meets = if !each then call(define(d), List(s))
      else LExpr.Forall(List(LBinder.Member(Names.builtin("x"), s)), call(define(d), List(name("x"))))
    LExpr.Forall(List(LBinder.Explicit(Names.builtin("s"), LowerType(ty))),
      LExpr.Infix(LOp.Arrow, call(define(initially), List(s)), meets))

  /** `∃ (x : T), (K.rule x)`. */
  private def inhabited(d: DefName, ty: Ty): LExpr =
    LExpr.Exists(List(LBinder.Explicit(Names.builtin("x"), LowerType(ty))), call(define(d), List(name("x"))))

  private def constant(c: Constant): LExpr = LowerValue(env)(c.value, c.ty).runA(closedNaming).value

  private val closedNaming = Naming.over(Set.empty, Set.empty)
  private def decl(n: NodeId, d: String): LExpr = LExpr.Const(Names.path(env.kb.value, n.value, d))
  private def define(d: DefName): LExpr = LExpr.Const(Names.path(env.kb.value, d.value))

  private def binders(opens: OpenTerms): List[LBinder] =
    Option.when(opens.sorts.nonEmpty)(LBinder.Several(opens.sorts.map(n => Names.ident(n.value)), name("Type")))
      .toList ++ opens.symbols.map(s => LBinder.Explicit(Names.ident(s.value), LowerType.binder(table.typeOf(s))))

object LowerProp:
  /** What a formula is over: the symbols it mentions, in order. */
  def opens(f: Written[Expr]): OpenTerms = OpenTerms(Nil, Exprs.mentions(f.value).symbols)
