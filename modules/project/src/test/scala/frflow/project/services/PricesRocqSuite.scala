package frflow.project.services

import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import frflow.eval.prices.{CounterExamples, CounterModel, PricesExamples, PricesModel, RatesExamples}
import frflow.eval.prices.RatesModel
import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.annotation.experimental
import scala.concurrent.duration.*

/** A structure no member changes (a plain trait, no `caps.Mutable`) and a structure whose class holds it, one whose
  * class holds that one in turn, and one whose class matches on an enum and an option, checked by Rocq end to end: each class is proven to meet the
  * claims on its word, and the examples hold in Rocq too.
  */
@experimental class PricesRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the claims on a structure no member changes, and on one that holds it, are proven".tag(Live)) {
    proven(PricesModel.model, PricesExamples())
  }

  test("the claims on a structure that reaches another through the one it holds are proven".tag(Live)) {
    proven(CounterModel.model, CounterExamples())
  }

  test("the claims on a structure whose class matches on an enum and an option are proven".tag(Live)) {
    proven(RatesModel.model, RatesExamples())
  }

  private def proven(model: FrModel, written: FrFlowExamples) =
    val examples = written.elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(model), examples, Nil).map { r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      examples.foreach(e => assertEquals(r.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).map(_.status), Some(ObligationStatus.Shown), e.name))
    }
