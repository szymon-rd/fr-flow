package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, Result}
import payments.PaymentsExamples
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The payment stream (`examples/payments`), checked by Rocq end to end: the class given for each word is
  * proven to meet the claims on it, the handler's from the claims on the card limits, the ledger and the offsets it is
  * made with; its examples hold on the code, those the two first versions fail on among them, and Rocq shows each
  * by running the code on the values it gives; every condition of a claim is shown possible, eight of them by the
  * values `Proofs/Payments/Whole.v` gives.
  */
@experimental class PaymentsRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = Ported.proofs("payments", "Payments")

  test("every claim of the stream is proven, its examples hold on the code, and no claim contradicts one".tag(Live)) {
    val examples = PaymentsExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(payments.payments), examples, proofs).map { r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      val whole = r.wholeCheck.toList.flatMap(_.results)
      examples.foreach { e =>
        def status(name: ObligationName) = whole.find(_.name == name).map(_.status)
        assertEquals(status(ObligationName.Example(e.of, e.at)), Some(ObligationStatus.Shown), e.name)
        assertEquals(status(ObligationName.ExampleOpposite(e.of, e.at)), Some(ObligationStatus.NotShown), e.name)
      }
      val possible = whole.collect { case Result(ObligationName.Satisfiable(_, _), status, _) => status }
      assertEquals((possible.size, possible.count(_ == ObligationStatus.Proven)), (22, 22))
    }
  }
