package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import payments.PaymentsExamples
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The payment stream (`examples/payments`), checked by Rocq end to end: the class given for each word is
  * proven to meet the claims on it, the handler's from the claims on the card limits, the ledger and the offsets it is
  * made with; its examples hold in Rocq too, those the two first versions fail on among them.
  */
@experimental class PaymentsRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = Ported.proofs("payments", "Payments")

  test("every claim of the stream is proven, and its examples hold in Rocq".tag(Live)) {
    val examples = PaymentsExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(payments.payments), examples, proofs).map { r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      // An example is shown by FrFlow's automation, or proven by hand (`Proofs/Payments/Whole.v`).
      val held = Set[ObligationStatus](ObligationStatus.Shown, ObligationStatus.Proven)
      examples.foreach(e => assert(r.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).exists(x => held(x.status)), e.name))
    }
  }
