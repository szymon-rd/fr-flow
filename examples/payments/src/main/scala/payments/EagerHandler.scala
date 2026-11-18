package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** A first version of the payment handler, kept for what it gets wrong: it commits before it applies. */
trait EagerHandler extends Mutable:
  /** Handles one payment: commits its offset, then has it authorised and posts it if it is approved. Whether it
    * is approved.
    */
  update def handle(payment: Payment): Boolean

object EagerHandler:
  val eager = Declaration[EagerHandler]("the handler's first version: it commits the offset, then applies the " +
    "payment")

  val eagerAppliesThePayment = Node.claim("Run to its end, the eager handler leaves the payment applied.")(
    forall((p: Term[Payment]) => PaymentHandler.applied(p.id, eager.handle(p).after)))

/** The handler with the commit first. Run to its end it leaves what the handler leaves; stopped after its first
  * step it has moved the committed offset past a payment that is not applied, and the log will not deliver it
  * again.
  */
final class CommitFirstHandler(limits: CardLimits^, ledger: Ledger^, offsets: ConsumerOffsets^)
    extends EagerHandler:
  update def handle(payment: Payment): Boolean =
    offsets.commit(payment.offset)
    val approved = limits.authorise(payment)
    if approved then ledger.post(payment)
    approved
