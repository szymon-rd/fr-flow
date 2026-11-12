package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** A first version of the processor: what it says of itself is what the processor says. */
trait Eager extends Mutable:
  update def handle(p: Payment): Boolean
  def applied(id: String): Boolean
  def position: BigInt

object Eager:
  val eager = Declaration[Eager]("the processor's first version: it commits the position, then applies the payment")

  val eagerAppliesThePayment = Node.claim("Run to its end, the eager processor leaves the payment applied.")(
    forall((p: Term[Payment]) => eager.applied(p.id).in(eager.handle(p).after)))

/** The processor with the commit first. Run to its end it leaves what the processor leaves; stopped after its
  * first step it has moved the position past a payment that is not applied, and the log will not deliver it again.
  */
final class EagerProcessor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^) extends Eager:
  update def handle(p: Payment): Boolean =
    checkpoint.commit(p.offset)
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    approved

  def applied(id: String): Boolean = limits.decided(id) && (!limits.approved(id) || accounts.posted(id))
  def position: BigInt = checkpoint.position
