package frflow.project.services

import frflow.project.{Live, Ported, Projects}
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The payment stream (`examples/payments`), checked by Lean end to end: the class given for each service is
  * proven to meet the claims on the service's Definition, the processor's from the claims on the services it is
  * made with.
  */
@experimental class PaymentsLeanSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private val proofs = List("Lemmas", "Whole", "authorisedIsRecorded", "authoriseIsRepeatable", "neverCommitsAhead")
    .map(n => n -> Ported.proof("payments", "Payments", n))

  test("every claim of the stream is proven".tag(Live)) {
    Ported.run(Projects.elaborated(payments.payments), Nil, Ported.Lean(proofs, Nil, None), Nil).map { r =>
      assertEquals(Ported.unproven(r.analysis), Map.empty, Ported.table(r.analysis))
    }
  }
