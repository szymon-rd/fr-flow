package frflow.proof.lean.laws

import frflow.core.{Booking, Lang}
import frflow.core.analysis.Reserved
import frflow.core.expr.{Expr, Exprs, LawSeeds, Renamed, Terms, Tm}
import frflow.core.name.{DefName, KbName, SymbolName}
import frflow.core.term.{Body, Bound, Final, Sym}
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.core.typing.{IrCheck, IrContext, Local}
import frflow.proof.lean.ast.{LExpr, Names}
import frflow.proof.lean.lower.{LowerEnv, Naming}
import frflow.proof.lean.print.Print
import frflow.proof.lean.term.Printed

/** The printer captures no name (the review's binder-capture and peephole probes, and their generalization): every
  * generated term, its binders named as Lean's keywords, prelude names, their mangled forms, the laws' types, models
  * and FrModel and the symbols themselves (`Renamed`), reads back (`LeanReader`) as it does printed with every
  * variable named afresh, up to the names of its variables (`DeBruijn`); and each symbol its IR mentions is free in
  * its Lean, as often.
  */
class CaptureLawsSuite extends munit.FunSuite:
  private val types = Set(Booking.name.value, MoreTerms.eventName.value, "World")
  private val symbols = (Renamed.symbols.keySet ++ Renamed.symbols.values).toSet
  private val naming = Naming.over(symbols ++ Reserved.names + LawsEnv.env.kb.value, types)
  private val terms: List[Final[Boolean]] = LawSeeds(300).flatMap(seed =>
    List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula).map(Renamed.of(_, seed)))

  private def printed(env: LowerEnv, n: Naming)(t: Final[Boolean]): String = Print.expr(Printed.formula(env, n)(t))
  private def read(s: String): LExpr = LeanReader(s).read()

  /** The same term with every variable named `x`, `x_1`, …, none a name the term's Lean holds. */
  private def afresh(env: LowerEnv, t: Final[Boolean]): String =
    val as = printed(env, naming)(t)
    printed(env, naming.copy(reserved = naming.reserved ++ LeanReader.tokens(as), canonical = true))(t)

  private def sameUpToNames(env: LowerEnv, t: Final[Boolean]): Unit =
    val text = printed(env, naming)(t)
    assertEquals(DeBruijn(read(text)), DeBruijn(read(afresh(env, t))), text)

  /** Each symbol the IR mentions, as Lean spells it, as often as it occurs. */
  private def mentioned(t: Final[Boolean]): List[String] =
    Exprs.all(ToExpr.of(t)).collect { case Expr.Sym(n, _) => Names.ident(n.value).text }.sorted

  test("the renamed terms name their binders as the symbols are named, raw and as Lean spells them") {
    val hints = terms.flatMap(t => Exprs.all(ToExpr.of(t)).flatMap(Exprs.binders)).map(_.hint).toSet
    assert(Set("some", "some_", "by", "x_1", "Laws", "Booking", "World", "a$b", "Except").subsetOf(hints), hints)
    val named = terms.flatMap(t => Exprs.mentions(ToExpr.of(t)).symbols.map(_.value)).toSet
    assert(Set("some", "by", "x_1", "a$b", "some_").subsetOf(named), named)
  }

  test("every term reads as it does with its variables named afresh: no variable takes another's name") {
    terms.foreach(sameUpToNames(LawsEnv.env, _))
  }

  test("every symbol the IR mentions is free in the term's Lean, as often: no binder captures one") {
    val spelled = symbols.map(Names.ident(_).text)
    terms.foreach { t =>
      val text = printed(LawsEnv.env, naming)(t)
      assertEquals(DeBruijn.free(read(text)).filter(spelled).sorted, mentioned(t), text)
    }
  }

  test("every renamed term's IR is well formed: each variable bound at its type, each node typed by its parts") {
    val check = IrCheck(Local(IrContext.open(LawsEnv.env.data, d => Option.when(d == Terms.positive.name)(Terms.fnTy))))
    terms.foreach(t => assertEquals(check(ToExpr.of(t)).toEither.map(_ => ()), Right(()), ToExpr.of(t)))
  }

  test("a pair's components are Lean's projections (p.1, p.2.1), never escaped as names") {
    val pair = frflow.core.term.Selector.second[BigInt, BigInt](Lang.big)
    val t: Final[Boolean] = [T[_]] => (s: Sym[T]) =>
      s.eq(s.field(s.param[(BigInt, BigInt)](SymbolName("p"), Ty.TupleOf(List(Lang.big, Lang.big))), pair),
        Lang(s).num(1))
    assertEquals(printed(LawsEnv.env, naming)(t), "(p.2 = (1 : Int))")
  }

  // The review's probes, each a term the printer once made a tautology of.

  private val some = SymbolName("some")
  private def forallSome(hint: String): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    s.forall(Bound[BigInt](hint, Lang.big))(x => s.eq(x, s.param[BigInt](some, Lang.big)))

  test("a binder named as a symbol's Lean (some_ beside some) takes another name: ∀ x, x = some is no tautology") {
    List("some_", "some", "some__").foreach { hint =>
      val text = printed(LawsEnv.env, naming)(forallSome(hint))
      assertEquals(DeBruijn.free(read(text)), List("Int", "some_"), text)
      sameUpToNames(LawsEnv.env, forallSome(hint))
    }
    assertEquals(printed(LawsEnv.env, Naming.over(Set("some"), types))(forallSome("some_")),
      "(∀ (some__ : Int), (some__ = some_))")
  }

  test("two names that once printed the same (a$b and a_b, some and some_) print apart") {
    assertEquals(List("a$b", "a_b", "some", "some_", "__x", "x_x", "by").map(Names.ident(_).text),
      List("«a$b»", "a_b", "some_", "some__", "«__x»", "x_x", "«by»"))
    assertEquals(List("Stored.inRoom_of", "matches", "a$b", "some").map(Names.define(_).text),
      List("Stored.inRoom_of", "«matches»", "«a$b»", "some"))
  }

  test("a binder named as the FrModel takes another name, so a define's call is not read as its field") {
    val positive = Terms.positive
    val t: Final[Boolean] = [T[_]] => (s: Sym[T]) =>
      s.forall(Bound[BigInt]("Laws", Lang.big))(x => s.app(s.define(positive), x))
    val text = printed(LawsEnv.env, naming)(t)
    assertEquals(text, "(∀ (Laws_1 : Int), (Laws.positive Laws_1))")
    sameUpToNames(LawsEnv.env, t)
  }

  /** A define of a FrModel named as the record it returns, its start the end it was given. */
  private val swapped: Body[String => BigInt => BigInt => Booking] = Body(DefName("swapped"),
    Ty.FnOf(List(Ty.Str, Lang.big, Lang.big), Booking.ty), [T[_]] => (s: Sym[T]) =>
      s.lam(Bound[String]("r", Ty.Str))(r => s.lam(Bound[BigInt]("st", Lang.big))(st =>
        s.lam(Bound[BigInt]("e", Lang.big))(e => s.app(s.app(s.app(s.construct(Booking.make), r), e), st)))))

  test("a field of a define's result is a field, though the FrModel is named as the record: no peephole on text") {
    val env = LawsEnv.env.copy(kb = KbName("Booking"))
    val t: Final[Boolean] = [T[_]] => (s: Sym[T]) =>
      s.forall(Bound[BigInt]("st", Lang.big))(st => s.forall(Bound[BigInt]("e", Lang.big))(e =>
        s.eq(s.field(s.app(s.app(s.app(s.define(swapped), Lang(s).str("Oak")), st), e), Booking.start), st)))
    assertEquals(printed(env, naming)(t),
      "(∀ (st : Int), (∀ (e : Int), ((Booking.swapped \"Oak\" st e).start = st)))")
  }

  test("a field of the record's constructor applied is its argument, read off the constructor") {
    val t: Final[Boolean] = [T[_]] => (s: Sym[T]) => s.forall(Bound[BigInt]("st", Lang.big))(st =>
      s.eq(s.field(s.app(s.app(s.app(s.construct(Booking.make), Lang(s).str("Oak")), st), st), Booking.end), st))
    assertEquals(printed(LawsEnv.env.copy(kb = KbName("Booking")), naming)(t), "(∀ (st : Int), ((st : Int) = st))")
  }
