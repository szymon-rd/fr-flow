package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** Another first version of the processor: what it says of itself is what the processor says. */
trait Hasty extends Mutable:
  update def handle(p: Payment): Boolean
  def approved(id: String): Boolean
  def posted(id: String): Boolean

object Hasty:
  val hasty = Definition[Hasty]("the processor's hasty version: it checks the limit itself, then has the " +
    "payment recorded")

  val hastyPostsWhatItApproves = Node.claim("A payment the hasty processor approves is posted.")(
    forall((p: Term[Payment]) => hasty.handle(p).result implies hasty.posted(p.id).in(hasty.handle(p).after)))

/** The processor with the check apart from the decision: it reads what the card has spent and the limit, decides
  * for itself, and then has the limits service record the payment. Alone it answers as the limits service does.
  * Among other calls its answer is stale: a payment the limits service declines is approved and posted.
  */
final class HastyProcessor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^) extends Hasty:
  update def handle(p: Payment): Boolean =
    val spent = limits.spent(p.card, p.day)
    val limit = limits.limit
    val fits = spent + p.amount <= limit
    limits.authorise(p): Unit
    if fits then accounts.post(p)
    checkpoint.commit(p.offset)
    fits

  def approved(id: String): Boolean = limits.approved(id)
  def posted(id: String): Boolean = accounts.posted(id)
