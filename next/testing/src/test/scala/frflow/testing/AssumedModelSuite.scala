package frflow.testing

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.eval.Semantics
import frflow.eval.assumed.Lookup
import frflow.core.name.{NodeId, SymbolName}
import frflow.testing.derive.Derive
import frflow.testing.model.{Difference, ModelRuns, ModelTests, Ran}
import frflow.testing.report.{Failure, Outcome}

/** The Scala of an operation known only by its assumptions (G2), tested against them on generated runs of its model's
  * operations: each call of it checked against what is assumed of its run (its result, the world it leaves), the
  * model given the state the Scala left. An index that answers right passes; one that never has a number breaks
  * `hasAnswers`, a seeded bug the runs find; with only `hasSound` assumed the same index meets what is assumed.
  */
class AssumedModelSuite extends munit.FunSuite:
  private def runs(kb: frflow.FrModel, forgets: Boolean): Outcome =
    val e = kb.elaborated.fold(es => fail(es.toString), identity)
    val model = e.theory.vocabulary.model(Lookup.register.name).getOrElse(fail("no model"))
    val impl = ModelTests.of(Lookup.register)(start = Lookup.Indexed.holding(_, forgets),
      observe = (i: Lookup.Indexed) => i.numbers)(i => (i.put, i.has))
    ModelRuns[IO](ModelTests.Check(model, impl), Semantics(e), e.theory).of(Plan(Settings.default, Nil),
      Derive.of(e, Nil)).unsafeRunSync().outcome

  test("an index that answers whether the register holds the number keeps what is assumed of it") {
    assertEquals(runs(Lookup.knowledge, forgets = false), Outcome.Passed)
  }

  test("an index that never has a number breaks hasAnswers: found by a generated run, at a call of has") {
    runs(Lookup.knowledge, forgets = true) match
      case Outcome.Failed(Failure.Run(_, _, Difference.Assumed(step, Ran.Gave(_), broken), _)) =>
        assertEquals((step.op, broken), (SymbolName("has"), List(NodeId("hasAnswers"))))
      case other => fail(s"not found: $other")
  }

  test("the same index meets what is assumed when only a yes is assumed right (hasSound)") {
    assertEquals(runs(Lookup.halfAssumed, forgets = true), Outcome.Passed)
  }
