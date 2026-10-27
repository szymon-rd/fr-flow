package frflow.eval.term

import frflow.core.Booking
import frflow.core.code.Values
import frflow.core.name.SymbolName
import frflow.core.expr.{Expr, Exprs, Terms, Tm}
import frflow.core.term.Final
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.{DataType, Ty}
import frflow.eval.Env
import frflow.proof.layout.{LeanTag, LeanWorkspace}
import frflow.proof.lean.ast.*
import frflow.proof.lean.laws.{LawsEnv, MoreTerms}
import frflow.proof.lean.lower.{LowerType, Naming}
import frflow.proof.lean.term.Printed

/** Lean decides each generated term as the evaluator does (`sbt leanTest`): the terms the printer's and the IR's laws
  * use (core's `Terms`, proof's `MoreTerms`), each made closed (`Closed`), evaluated in Scala, and stated in Lean as
  * that value (the term, or its negation), proven by `decide` or by FrFlow's `frflow_eval`, which decides examples.
  * A program's runs are from one world (`Closed.before`), of programs Lean and Scala each hold (`LawPrograms`,
  * `Closed.programs`), a failing one's `Except` arms among them. A term with no Scala value (a quantifier over a
  * whole type, the world outside) is left out.
  */
class LeanDecidesSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  private val naming = Naming.over(Set.empty, Set(Booking.name.value, MoreTerms.eventName.value, "World"))
  private val generated: List[Final[Boolean]] =
    (1L to 600L).toList.flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))
  private val programs = Values(Closed.programs.map((p, f) => SymbolName(p) -> (() => f)))
  /** Each closed term with a Scala value, and that value. */
  private val decided: List[(Final[Boolean], Boolean)] = generated.map(Closed.of).filterNot(open).flatMap(t =>
    Evaluate.of(t)(Env.of(programs)).toOption.map(t -> _))

  private def open(t: Final[Boolean]): Boolean = Exprs.all(ToExpr.of(t)).exists {
    case Expr.Quant(_, _, _) | Expr.Outside(_) => true
    case _                                     => false
  }

  private def n(s: String): LeanName = Names.builtin(s)
  private def x(s: String, t: LExpr): LBinder = LBinder.Explicit(Names.ident(s), t)
  private def fields(d: DataType): List[(LeanName, LExpr)] = d match
    case DataType.Product(_, _, fs) => fs.map(f => Names.ident(f.name) -> LowerType(f.ty))
    case _                          => Nil
  private val types: List[Decl] = List(
    Decl.Structure(n("Booking"), fields(Booking.data)),
    Decl.Inductive(n("Event"), List(n("Booked") -> List(x("at", LExpr.Name(n("Int")))), n("Cleared") -> Nil)),
    Decl.Structure(n("World"), List(n("stored") -> LExpr.Name(n("Int")))),
    Decl.Def(List(Attr.FrflowDefs), n("positive"), Nil, LowerType.binder(Terms.fnTy),
      Printed.formula(LawsEnv.env, naming)(Terms.positive.body))) ++ LawPrograms.decls

  /** The term as its value says: itself when true, its negation when false. */
  private def theorem(t: Final[Boolean], holds: Boolean, i: Int): Decl =
    val term = Printed.formula(LawsEnv.env, naming)(t)
    val statement = if holds then term else LExpr.Prefix(LPrefix.NotSpaced, LExpr.Paren(term))
    Decl.Theorem(Nil, n(s"t_$i"), Nil, statement, Proof.Tactics(tactics), Break.SameLine)
  private val tactics = List("first", "  | decide", "  | frflow_eval", "  | simp_all [frflow_defs]")

  /** Lean's verdict on the terms stated with the values given: whether every one is proven, and Lake's output. */
  private def proven(name: String, values: List[(Final[Boolean], Boolean)]): (Boolean, String) =
    val m = LeanModule(ModuleName(Names.path("FrFlowGen", "Laws", "Decided")), List(ModuleName(Names.path("FrFlow"))),
      Preamble.generated, Names.path("Laws"), Nil, types ++ values.zipWithIndex.map { case ((t, v), i) =>
        theorem(t, v, i) })
    LeanWorkspace.make(name).build(List(m))

  test("most generated terms have a Scala value, both true and false among them") {
    assert(decided.size >= 300, decided.size)
    assert(decided.exists(_._2) && decided.exists(!_._2), decided.map(_._2).distinct)
    assert(decided.forall((t, _) => Exprs.typeOf(ToExpr.of(t)) == Ty.Bool))
    val runs = decided.flatMap((t, _) => Exprs.all(ToExpr.of(t)).collect { case r: Expr.Runs => r.failing })
    assert(runs.contains(true) && runs.contains(false), runs.distinct)
  }

  test("Lean decides each generated term as the evaluator does".tag(LeanTag)) {
    val (built, out) = proven("decided", decided)
    assert(built, out.linesIterator.take(80).mkString("\n"))
  }

  test("a term stated with the other value is not proven: the law can fail".tag(LeanTag)) {
    val (t, v) = decided.head
    val (built, out) = proven("undecided", List(t -> !v))
    assert(!built && out.contains("error: FrFlowGen/Laws/Decided.lean"), out)
  }

  test("a closed term's symbols are gone: its IR names none the generators give a value") {
    val names = decided.flatMap((t, _) => Exprs.mentions(ToExpr.of(t)).symbols.map(_.value)).toSet
    assertEquals(names & Set("p", "k", "xs", "o", "slot", "s", "m", "ev", "outcome"), Set.empty[String])
  }
