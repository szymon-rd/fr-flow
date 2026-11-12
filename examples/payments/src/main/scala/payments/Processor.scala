package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The processor: it handles one payment from the log, and says where the stream stands. */
trait Processor extends Mutable:
  /** Handles a payment: whether it is approved. */
  update def handle(p: Payment): Boolean
  /** A payment is applied: it was decided, and if it was approved it is posted. */
  def applied(id: String): Boolean
  /** A payment not yet decided fits its card's limit of the day. */
  def fits(p: Payment): Boolean
  def position: BigInt
  def spent(card: String, day: BigInt): BigInt
  def limit: BigInt
  def total: BigInt
  def posted(id: String): Boolean
  def postingsOf(id: String): List[Posting]

object Processor:
  val processor = Definition[Processor]("the processor: it handles one payment from the log")

  val handledIsApplied = Node.claim("A payment handled is applied: decided, and posted if approved.")(
    forall((p: Term[Payment]) => processor.applied(p.id).in(processor.handle(p).after)))

  val appliedStaysApplied = Node.claim("Handling a payment leaves every payment applied before applied.")(
    forall((id: Term[String], p: Term[Payment]) =>
      processor.applied(id) implies processor.applied(id).in(processor.handle(p).after)))

  val positionMovesPastTheHandled = Node.claim("Handling the payment the position is at moves the position " +
      "one past it.")(
    forall((p: Term[Payment]) =>
      (processor.position === p.offset) implies
        (processor.position.in(processor.handle(p).after) === p.offset + 1)))

  val redeliveryChangesNothing = Node.claim("A payment handled again gets the answer it got and changes " +
      "nothing.")(
    forall((p: Term[Payment]) =>
      (processor.handle(p).in(processor.handle(p).after).result === processor.handle(p).result) &&
        (processor.handle(p).in(processor.handle(p).after).after === processor.handle(p).after)))

  val fittingIsApproved = Node.claim("A payment not yet decided that fits its card's limit of the day is " +
      "approved.")(
    forall((p: Term[Payment]) => processor.fits(p) implies processor.handle(p).result))

  val handlingKeepsWithinLimit = Node.claim("Handling a payment leaves a card within its limit of a day within " +
      "it.")(
    forall((card: Term[String], day: Term[BigInt], p: Term[Payment]) =>
      (processor.spent(card, day) <= processor.limit) implies
        (processor.spent(card, day).in(processor.handle(p).after) <=
          processor.limit.in(processor.handle(p).after))))

  val moneyIsConserved = Node.claim("Handling a payment makes no money and destroys none.")(
    forall((p: Term[Payment]) => processor.total.in(processor.handle(p).after) === processor.total))

  val handlingKeepsMarks = Node.claim("Handling a payment leaves a payment that has postings only if it is " +
      "marked so.")(
    forall((id: Term[String], p: Term[Payment]) =>
      (processor.postingsOf(id).isEmpty || processor.posted(id)) implies
        (processor.postingsOf(id).in(processor.handle(p).after).isEmpty ||
          processor.posted(id).in(processor.handle(p).after))))

  val postedOnce = Node.claim("Handling a payment adds nothing to the postings of a payment that has some, " +
      "where a payment with postings is marked.")(
    forall((id: Term[String], p: Term[Payment]) =>
      (processor.postingsOf(id).isEmpty || processor.posted(id)) implies
        (processor.postingsOf(id).isEmpty ||
          processor.postingsOf(id).in(processor.handle(p).after) === processor.postingsOf(id))))

/** The processor over the three services. It has the limits service decide the payment, has the accounts service
  * post it if it is approved, and only then commits the position past it. Each step can be repeated, so a payment
  * delivered again, to this instance after a crash or to another after a rebalance, is applied once.
  */
final class StreamProcessor(limits: Limits^, accounts: Accounts^, checkpoint: Checkpoint^) extends Processor:
  update def handle(p: Payment): Boolean =
    val approved = limits.authorise(p)
    if approved then accounts.post(p)
    checkpoint.commit(p.offset)
    approved

  def applied(id: String): Boolean = limits.decided(id) && (!limits.approved(id) || accounts.posted(id))
  def fits(p: Payment): Boolean = !limits.decided(p.id) && limits.spent(p.card, p.day) + p.amount <= limits.limit
  def position: BigInt = checkpoint.position
  def spent(card: String, day: BigInt): BigInt = limits.spent(card, day)
  def limit: BigInt = limits.limit
  def total: BigInt = accounts.total
  def posted(id: String): Boolean = accounts.posted(id)
  def postingsOf(id: String): List[Posting] = accounts.postingsOf(id)
