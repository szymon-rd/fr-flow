package frflow.eval.term

import frflow.core.code.Values
import frflow.core.name.SymbolName
import frflow.core.expr.{Expr, Exprs, LawSeeds, Terms, Tm}
import frflow.core.term.Final
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.eval.Env
import frflow.proof.layout.LeanTag
import frflow.proof.lean.laws.MoreTerms

/** Lean decides each generated term as the evaluator does (`sbt leanTest`): the terms the printer's and the IR's laws
  * use (core's `Terms`, proof's `MoreTerms`), each made closed (`Closed`: its symbols given values, the world outside
  * assumed), the DSL's (`DslTerms`) and the hand-written `Extras`; evaluated in Scala, and stated in Lean as that
  * value, proven by `decide` or by FrFlow's `frflow_eval`, which decides examples (`LawModules`). A program's runs are
  * from one world (`Closed.before`), of programs Lean and Scala each hold (`LawPrograms`, `Closed.programs`), a failing
  * one's `Except` arms among them. A term with no Scala value (a quantifier over a whole type) is left out. Stated with
  * the other value, no term is proven: the law fails on any term the two disagree on.
  */
class LeanDecidesSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  private val generated: List[Final[Boolean]] =
    LawSeeds(600).flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))
  private val programs = Values(Closed.programs.map((p, f) => SymbolName(p) -> (() => f)))
  /** Each closed term with a Scala value, and that value. */
  private val decided: List[(Final[Boolean], Boolean)] =
    (generated.map(Closed.of) ++ Extras.terms ++ DslTerms.terms).filterNot(open)
      .flatMap(t => Evaluate.of(t)(Env.of(programs)).toOption.map(t -> _))

  private def open(t: Final[Boolean]): Boolean = Exprs.all(ToExpr.of(t)).exists {
    case Expr.Quant(_, _, _) => true
    case _                   => false
  }
  private def all(t: Final[Boolean]): List[Expr] = Exprs.all(ToExpr.of(t))

  test("most terms have a Scala value, both true and false among them, every kind of operation reached") {
    assert(decided.size >= 750, decided.size)
    assert(decided.exists(_._2) && decided.exists(!_._2), decided.map(_._2).distinct)
    assert(decided.forall((t, _) => Exprs.typeOf(ToExpr.of(t)) == Ty.Bool))
    val runs = decided.flatMap((t, _) => all(t).collect { case r: Expr.Runs => r.failing })
    assert(runs.contains(true) && runs.contains(false), runs.distinct)
    val ops = decided.flatMap((t, _) => all(t).collect { case Expr.Prim(op, _, _) => op.toString })
    val few = List("Union", "Incl", "Contains", "Updated", "Get").map(op => op -> ops.count(_ == op)).filter(_._2 < 8)
    assertEquals(few, Nil)
  }

  test("the unchanged worlds compare the models' states, the faults aside") {
    assertEquals(Extras.terms.map(t => Evaluate.of(t)(Env.of(Values.none))),
      List(Right(true), Right(true), Right(false), Right(true), Right(false), Right(false)))
  }

  test("Lean decides each term as the evaluator does".tag(LeanTag)) {
    val (proven, out) = LawModules.verdicts("Decided", decided)
    assert(proven.size == decided.size && proven.forall(identity) && !out.contains("error:"),
      out.linesIterator.take(80).mkString("\n"))
  }

  test("each term stated with the other value is not proven: the law fails on any disagreement".tag(LeanTag)) {
    val (proven, out) = LawModules.verdicts("Negated", decided.map((t, v) => t -> !v))
    assertEquals(proven.size, decided.size, out.linesIterator.take(40).mkString("\n"))
    assertEquals(proven.zipWithIndex.collect { case (true, i) => i }, Nil)
  }

  test("a closed term's symbols are gone: its IR names none the generators give a value") {
    val names = decided.flatMap((t, _) => Exprs.mentions(ToExpr.of(t)).symbols.map(_.value)).toSet
    assertEquals(names & Set("p", "k", "xs", "o", "slot", "s", "m", "ev", "outcome"), Set.empty[String])
  }
