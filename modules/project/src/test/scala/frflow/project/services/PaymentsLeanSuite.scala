package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.ObligationStatus
import payments.PaymentsExamples
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The payment stream (`examples/payments`), checked by Lean end to end: the class given for each service is
  * proven to meet the claims on the service's Definition, the processor's from the claims on the services it is
  * made with; its examples hold in Lean too, those the two first versions fail on among them.
  */
@experimental class PaymentsLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = List("Lemmas", "Whole", "authorisedIsRecorded", "authoriseIsRepeatable", "neverCommitsAhead")
    .map(n => n -> Ported.proof("payments", "Payments", n))

  test("every claim of the stream is proven, and its examples hold in Lean".tag(Live)) {
    val examples = PaymentsExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(payments.payments), examples, Ported.Lean(proofs, Nil, None), Nil).map { r =>
      assertEquals(Ported.unproven(r.analysis), Map.empty, Ported.table(r.analysis))
      assertEquals(r.analysis.computed.examples.map(_._2).distinct, List(OnCode.Holds))
      // An example is shown by FrFlow's automation, or proven by hand (`Proofs/Payments/Whole.lean`).
      val held = Set[ObligationStatus](ObligationStatus.Shown, ObligationStatus.Proven)
      examples.foreach(e => assert(r.analysis.wholeCheck.flatMap(_.results.find(_.name ==
        ObligationName.Example(e.of, e.at))).exists(x => held(x.status)), e.name))
    }
  }
