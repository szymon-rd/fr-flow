package frflow.project.services

import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import frflow.eval.prices.{PricesExamples, PricesModel, RatesExamples, RatesModel}
import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import scala.annotation.experimental
import scala.concurrent.duration.*

/** A structure no member changes (a plain trait, no `caps.Mutable`) and a structure whose class holds it, and one
  * whose class matches on an enum and an option, checked by Lean end to end: each class is proven to meet the
  * claims on its word, and the examples hold in Lean too.
  */
@experimental class PricesLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the claims on a structure no member changes, and on one that holds it, are proven".tag(Live)) {
    proven(PricesModel.model, PricesExamples())
  }

  test("the claims on a structure whose class matches on an enum and an option are proven".tag(Live)) {
    proven(RatesModel.model, RatesExamples())
  }

  private def proven(model: FrModel, written: FrFlowExamples) =
    val examples = written.elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(model), examples, Ported.Lean(Nil, Nil, None), Nil).map { r =>
      assertEquals(Ported.unproven(r.analysis), Map.empty, Ported.table(r.analysis))
      assertEquals(r.analysis.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      examples.foreach(e => assertEquals(r.analysis.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).map(_.status), Some(ObligationStatus.Shown), e.name))
    }
