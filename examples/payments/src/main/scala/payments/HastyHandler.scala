package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import Ledger.ledger

/** Another first version of the payment handler, kept for what it gets wrong: it checks the limit itself. */
trait HastyHandler extends Mutable:
  /** Handles one payment: checks its card's limit itself, has the payment recorded, posts it if it found it to
    * fit, and commits its offset. Whether it found it to fit.
    */
  update def handle(payment: Payment): Boolean

object HastyHandler:
  val hasty = Declaration[HastyHandler]("the handler's hasty version: it checks the limit itself, then has the " +
    "payment recorded")

  val hastyPostsWhatItApproves = Node.claim("A payment the hasty handler approves is posted.")(
    forall((p: Term[Payment]) => hasty.handle(p).result implies ledger.posted(p.id).in(hasty.handle(p).after)))

/** The handler with the check apart from the decision: it reads what the card has spent and the limit, decides
  * for itself, and then has the card limits record the payment. Alone it answers as the card limits do. Among
  * other calls its answer is stale: a payment the card limits decline is approved and posted.
  */
final class CheckThenActHandler(limits: CardLimits^, ledger: Ledger^, offsets: ConsumerOffsets^)
    extends HastyHandler:
  update def handle(payment: Payment): Boolean =
    val spent = limits.spent(payment.card, payment.day)
    val limit = limits.dailyLimit
    val fits = spent + payment.amount <= limit
    limits.authorise(payment): Unit
    if fits then ledger.post(payment)
    offsets.commit(payment.offset)
    fits
