package frflow.proof.prover.lower

import cats.data.Writer
import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{DefName, ProverNames, NodeId, SymbolName, TypeName}
import frflow.core.spec.{Form, Written}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.*
import frflow.proof.prover.term.Printed
import frflow.proof.obligation.{Constant, Hyp, Prop, Substitute}
import frflow.proof.terms.{OpenTerms, TermTable}

/** A proposition as a Lean statement: each declaration applied to its open terms, each term replaced by its
  * substitute; the open terms left are bound by `Forall` (or `Exists`) in the order met
  * (the claims it is about, the conclusion, the hypotheses), then the hypotheses `h_<Node>`. A value provided where
  * the code runs comes with what always holds of it (`fromOutside`), wherever it is bound. A Definition with a
  * meaning of its own (`meant`: proven code, a fixed value, or a value provided where the code runs, which
  * a statement takes for every value) is never bound by `∃` but where named. Every term is printed in the theory's
  * `naming`, so no variable takes a name a symbol prints as. Today's `Refinement.claim`, `stated` and
  * `Vocabulary.term`, on values.
  */
final class LowerProp[E](table: TermTable, env: LowerEnv, naming: Naming, values: LowerProp.Values[E])(using
    syntax: Syntax[E], seen: Seen[E]):
  private val atoms = new Atoms(syntax)
  import atoms.{call, name}
  private val types = new LowerType(syntax)
  private type Quantifier = (List[Binding[E]], E) => E
  private val (fromOutside, meant) = (values.fromOutside, values.meant)
  private type W[A] = Writer[OpenTerms, A]
  private type Subst = Map[SymbolName, Substitute]

  def statement(p: Prop): E = p match
    case Prop.Forall(about, body) => closed(about, body, LOp.Arrow)(syntax.forall(_, _))
    case Prop.Exists(about, body) => closed(about, body, LOp.And)(syntax.exists(_, _))
    case Prop.ForEvery(ss, body)  => named(ss, body, LOp.Arrow, Nil)(syntax.forall(_, _))
    case Prop.ForSome(ss, body)   => named(ss, body, LOp.And, Nil)(syntax.exists(_, _))
    case other                   => prop(other, Map.empty).value

  /** `∀`/`∃` `ss`, each at its type, then what the body leaves open beside them and what is bound outside (`outer`):
    * what the code standing in it is over; nothing to bind, the body alone. Under `∃` a Definition with a meaning of
    * its own left in the body is not bound: a proof would choose its meaning, not its code's (a consistency
    * statement must have the code stand in it, `Stands`), so it is left unbound and Lean refuses the statement, a
    * FrFlow bug failing closed. Under `∀` it is bound: the statement holds of every meaning, its code's among them.
    */
  private def named(ss: List[SymbolName], body: Prop, op: LOp, outer: List[SymbolName])(q: Quantifier): E =
    val (opens, b) = body match
      case Prop.ForEvery(ts, inside) =>
        (OpenTerms.empty, named(ts, inside, LOp.Arrow, outer ++ ss)(syntax.forall(_, _)))
      case Prop.ForSome(ts, inside)  => (OpenTerms.empty, named(ts, inside, LOp.And, outer ++ ss)(syntax.exists(_, _)))
      case Prop.Forall(_, _) | Prop.Exists(_, _) => (OpenTerms.empty, statement(body))
      case other                     => prop(other, Map.empty).run
    val left = opens.symbols.filterNot(s => outer.contains(s) || (op == LOp.And && meant(s)))
    val all = OpenTerms(if outer.isEmpty then opens.sorts else Nil, (ss ++ left).distinct)
    if all.symbols.isEmpty && all.sorts.isEmpty then b else q(binders(all), hypotheses(all.symbols, b, op))

  private def closed(about: List[NodeId], body: Prop, op: LOp)(q: Quantifier): E =
    val (opens, b) = (about.traverse(n => prop(Prop.claim(n), Map.empty)) *> withHyps(body)).run
    binders(opens) match
      case Nil => b
      case bs  => q(bs, hypotheses(opens.symbols, b, op))

  /** What always holds of each provided value among `ss`, before the body: each a hypothesis named by
    * `outsideNames` under `∀` (so a proof applies it by name), conjoined (`∧`) under `∃`.
    */
  private def hypotheses(ss: List[SymbolName], body: E, op: LOp): E = op match
    case LOp.And => fromOutsideOf(ss).foldRight(body)(syntax.infix(op, _, _))
    case _       =>
      ss.flatMap(s => outsideNames(s).zip(fromOutside(s))).foldRight(body)((nh, b) =>
        syntax.forall(List(Binding.Explicit(nh._1, nh._2)), b))

  def fromOutsideOf(ss: List[SymbolName]): List[E] = ss.flatMap(fromOutside)

  /** The names of the hypotheses on a provided value, `o_<value>_<i>`, as every statement binding it names them. */
  def outsideNames(s: SymbolName): List[ProverName] =
    fromOutside(s).indices.toList.map(i => Names.builtin(ProverNames.outside(s, i)))

  /** The open terms a statement binds, in order: what `statement` quantifies over. */
  def opens(p: Prop): OpenTerms = p match
    case Prop.Forall(about, body) => (about.traverse(n => prop(Prop.claim(n), Map.empty)) *> withHyps(body)).run._1
    case Prop.Exists(about, body) => opens(Prop.Forall(about, body))
    case other                    => prop(other, Map.empty).run._1

  /** `∀ (h_A : …) (h_B : …), c` for an implication at the top of a statement. */
  private def withHyps(p: Prop): W[E] = p match
    case Prop.Implies(Nil, c) => prop(c, Map.empty)
    case Prop.Implies(hs, c)  => (prop(c, Map.empty), hs.traverse(hyp)).mapN((x, bs) => syntax.forall(bs, x))
    case other                => prop(other, Map.empty)

  private def hyp(h: Hyp): W[Binding[E]] = prop(h.prop, Map.empty).map(Binding.Explicit(Names.builtin(h.name), _))

  def prop(p: Prop, σ: Subst): W[E] = p match
    case Prop.ClaimOf(n, more)   => applied(decl(n, "claim"), table.claims.getOrElse(n, OpenTerms.empty), σ ++ more)
    case Prop.Makes(i, op, f, m) => applied(decl(i, ProverNames.makes(op.value)), LowerKeeps.opens(f, table), σ ++ m)
    case Prop.ConjunctOf(n, i)   =>
      applied(decl(n, ProverNames.conjunct(i)), table.claims.getOrElse(n, OpenTerms.empty), σ)
    case Prop.Inhabited(d, ty)   => Writer.value(inhabited(d, ty))
    case Prop.Iff(a, b)          => (prop(a, σ), prop(b, σ)).mapN((x, y) => syntax.paren(syntax.infix(LOp.Iff, x, y)))
    case Prop.Both(ps)           => ps.traverse(prop(_, σ)).map(_.toList.reduceRight(syntax.infix(LOp.And, _, _)))
    case Prop.Not(a)             => prop(a, σ).map(syntax.prefix(LPrefix.NotSpaced, _))
    case Prop.False              => Writer.value(name("False"))
    case Prop.Implies(hs, c)     => (hs.traverse(h => prop(h.prop, σ)), prop(c, σ)).mapN((xs, y) =>
                                      (xs :+ y).reduceRight(syntax.infix(LOp.Arrow, _, _)))
    case Prop.Formula(w, code)   => formula(w, σ ++ code)
    case Prop.Forall(_, _) | Prop.Exists(_, _) => Writer.value(syntax.paren(statement(p)))
    case Prop.ForEvery(ss, body) => inner(ss, body, σ, LOp.Arrow)(syntax.forall(_, _))
    case Prop.ForSome(ss, body)  => inner(ss, body, σ, LOp.And)(syntax.exists(_, _))

  /** A statement inside another binding exactly `ss`: the open terms it leaves are the enclosing statement's. */
  private def inner(ss: List[SymbolName], body: Prop, σ: Subst, op: LOp)(q: Quantifier): W[E] =
    val (opens, b) = prop(body, σ).run
    val left = OpenTerms((opens.sorts ++ ss.flatMap(leaf(_).sorts)).distinct, opens.symbols.filterNot(ss.contains))
    Writer(left, if ss.isEmpty then b else syntax.paren(q(binders(OpenTerms(Nil, ss)), hypotheses(ss, b, op))))

  /** A formula printed from its term (`Printed`), each symbol as `σ` writes it, its open terms told: the symbols its
    * IR (`Written.value`, made once when elaborated) mentions, through what stands for them.
    */
  private def formula(w: Written[Expr], σ: Subst): W[E] = w.form match
    case Form.Term(t) =>
      val said = Exprs.mentions(w.value)
      val mentioned = (said.symbols ++ said.defines.flatMap(table.defines.getOrElse(_, OpenTerms.empty).symbols))
        .distinct
      val (opens, standing) = mentioned.traverse(x =>
        if σ.contains(x) then symbol(x, σ).map(e => List(x -> e)) else Writer(OpenTerms(Nil, List(x)), Nil)).run
      Writer(opens, Printed.standing[E](env, naming, 0, standing.flatten.toMap)(t))

  /** `f` applied to its open terms: `(Crm.ExpiryJob.claim expire runExpiry)`, or `f` alone over none. */
  private def applied(f: E, terms: OpenTerms, σ: Subst): W[E] =
    (terms.sorts.traverse(sort), terms.symbols.traverse(symbol(_, σ))).mapN(_ ++ _)
      .map(args => if args.isEmpty then f else call(f, args))

  private def sort(t: TypeName): W[E] = Writer.tell(OpenTerms(List(t), Nil)).as(syntax.name(Names.ident(t.value)))

  /** A define applied to its open terms, each a value `known` gives it or its name: proven code inside a witness. */
  def code(d: DefName, known: Map[SymbolName, E]): E =
    val terms = table.defines.getOrElse(d, OpenTerms.empty)
    val args = terms.sorts.map(n => syntax.name(Names.ident(n.value))) ++
      terms.symbols.map(s => known.getOrElse(s, syntax.name(Names.ident(s.value))))
    if args.isEmpty then define(d) else call(define(d), args)

  /** What a symbol is written as under `σ`: its substitute applied to its own open terms, or its name. */
  def standing(s: SymbolName, σ: Subst): E = symbol(s, σ).value

  private def symbol(s: SymbolName, σ: Subst): W[E] = σ.get(s) match
    case Some(Substitute.Code(d)) => applied(define(d), table.defines.getOrElse(d, OpenTerms.empty), σ)
    case Some(Substitute.Fixed(c)) => Writer.value(constant(c))
    case Some(Substitute.Nothing) => Writer.value(atoms.nothing(naming, table.typeOf(s)))
    case None                     => Writer.tell(leaf(s)).as(syntax.name(Names.ident(s.value)))

  private def leaf(s: SymbolName): OpenTerms =
    OpenTerms(Ty.parts(table.typeOf(s)).collect { case Ty.Sort(n) => n }.distinct, List(s))

  /** A define on its open terms, each named as itself. */
  private def opened(d: DefName): E =
    applied(define(d), table.defines.getOrElse(d, OpenTerms.empty), Map.empty).value

  /** `∀ opens, body`: what the defines given are over, bound (nothing when they are over nothing). */
  private def overOpens(ds: List[DefName], body: E): E =
    val opens = ds.flatMap(d => table.defines.getOrElse(d, OpenTerms.empty).symbols).distinct
    if opens.isEmpty then body else syntax.forall(binders(OpenTerms(Nil, opens)), body)

  /** `∃ (x : T), (K.rule x)`. */
  private def inhabited(ds: List[DefName], ty: Ty): E =
    val x = Naming.helper("x", Set.empty).runA(naming).value
    overOpens(ds, syntax.exists(List(Binding.Explicit(x, types(ty))),
      ds.map(d => call(opened(d), List(syntax.name(x)))).reduceRightOption(syntax.infix(LOp.And, _, _))
        .getOrElse(name("True"))))

  private def constant(c: Constant): E = new LowerValue[E](env).apply(c.value, c.ty).runA(naming).value
  private def decl(n: NodeId, d: String): E = syntax.const(Names.path(env.kb.value, n.value, d))
  private def define(d: DefName): E = syntax.const(List(Names.builtin(env.kb.value), Names.define(d.value)))

  private def binders(opens: OpenTerms): List[Binding[E]] =
    Option.when(opens.sorts.nonEmpty)(Binding.Several(opens.sorts.map(n => Names.ident(n.value)), name("Type")))
      .toList ++ opens.symbols.map(s => Binding.Explicit(Names.ident(s.value), types.binder(table.typeOf(s))))

object LowerProp:
  /** What always holds of a value provided where the code runs, and whether a Definition has a meaning of its own. */
  final case class Values[E](fromOutside: SymbolName => List[E], meant: SymbolName => Boolean = _ => false)
