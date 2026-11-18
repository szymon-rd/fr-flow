package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import CardLimits.limits
import ConsumerOffsets.offsets
import Ledger.ledger

/** Handles the card payments read from the log, one at a time. */
trait PaymentHandler extends Mutable:
  /** Handles one payment: has it authorised, posts it if it is approved, and commits its offset. Whether it is
    * approved.
    */
  update def handle(payment: Payment): Boolean

/** What must hold of a payment handler, said of the card limits, the ledger and the consumer's offsets it holds:
  * a claim asks them what they say (`ledger.posted(id)`) as the handler has them.
  */
object PaymentHandler:
  val handler = Declaration[PaymentHandler]("the payment handler: it handles one payment from the log")

  /** A payment is applied, as a handler in the state `in` has things: decided, and posted if approved. */
  def applied[H <: String](id: Term[PaymentId], in: Term[StateOf[H]])(using Stating): Term[Boolean] =
    limits.decided(id).in(in) && (!limits.approved(id).in(in) || ledger.posted(id).in(in))

  /** A payment not yet decided fits its card's limit of the day, by the limits as they stand. */
  private def fits(p: Term[Payment])(using Stating): Term[Boolean] =
    !limits.decided(p.id) && (limits.spent(p.card, p.day) + p.amount <= limits.dailyLimit)

  /** A payment has no postings unless it is marked as posted, as a handler in the state `in` has the ledger. */
  private def marked[H <: String](id: Term[PaymentId], in: Term[StateOf[H]])(using Stating): Term[Boolean] =
    ledger.postingsOf(id).in(in).isEmpty || ledger.posted(id).in(in)

  val handledIsApplied = Node.claim("A payment handled is applied: decided, and posted if approved.")(
    forall((p: Term[Payment]) => applied(p.id, handler.handle(p).after)))

  val appliedStaysApplied = Node.claim("Handling a payment leaves every payment applied before applied.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      applied(id, handler.current) implies applied(id, handler.handle(p).after)))

  val offsetMovesPastTheHandled = Node.claim("Handling the payment at the committed offset moves that offset " +
      "one past it.")(
    forall((p: Term[Payment]) =>
      (offsets.committed === p.offset) implies
        (offsets.committed.in(handler.handle(p).after) === p.offset + 1)))

  val redeliveryChangesNothing = Node.claim("A payment handled again gets the answer it got and changes " +
      "nothing.")(
    forall((p: Term[Payment]) =>
      (handler.handle(p).in(handler.handle(p).after).result === handler.handle(p).result) &&
        (handler.handle(p).in(handler.handle(p).after).after === handler.handle(p).after)))

  val fittingIsApproved = Node.claim("A payment not yet decided that fits its card's limit of the day is " +
      "approved.")(
    forall((p: Term[Payment]) => fits(p) implies handler.handle(p).result))

  val handlingKeepsWithinLimit = Node.claim("Handling a payment leaves a card within its limit of a day within " +
      "it.")(
    forall((card: Term[CardId], day: Term[BigInt], p: Term[Payment]) =>
      (limits.spent(card, day) <= limits.dailyLimit) implies
        (limits.spent(card, day).in(handler.handle(p).after) <= limits.dailyLimit.in(handler.handle(p).after))))

  val moneyIsConserved = Node.claim("Handling a payment makes no money and destroys none.")(
    forall((p: Term[Payment]) => ledger.total.in(handler.handle(p).after) === ledger.total))

  val handlingKeepsMarks = Node.claim("Handling a payment leaves a payment that has postings only if it is " +
      "marked so.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      marked(id, handler.current) implies marked(id, handler.handle(p).after)))

  val postedOnce = Node.claim("Handling a payment adds nothing to the postings of a payment that has some, " +
      "where a payment with postings is marked.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      marked(id, handler.current) implies
        (ledger.postingsOf(id).isEmpty ||
          ledger.postingsOf(id).in(handler.handle(p).after) === ledger.postingsOf(id))))

  // Every step of handling a payment, whatever other calls do between the steps: another instance handling
  // payments after a rebalance.

  val everyStepKeepsWithinLimit = Node.claim("No step of handling a payment takes a card over its limit of a " +
      "day, whatever other calls do between the steps.")(
    forall((card: Term[CardId], day: Term[BigInt], p: Term[Payment]) =>
      handler.handle(p).amongOthers(run => run.steps.forall(step =>
        (limits.spent(card, day).in(step._1) <= limits.dailyLimit.in(step._1)) implies
          (limits.spent(card, day).in(step._2) <= limits.dailyLimit.in(step._2))))))

  val noStepMakesMoney = Node.claim("No step of handling a payment makes money or destroys it.")(
    forall((p: Term[Payment]) =>
      handler.handle(p).amongOthers(run => run.steps.forall(step =>
        ledger.total.in(step._2) === ledger.total.in(step._1)))))

  val noStepPostsTwice = Node.claim("No step of handling a payment adds to the postings of a payment that has " +
      "some, where a payment with postings is marked.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      handler.handle(p).amongOthers(run => run.steps.forall(step =>
        marked(id, step._1) implies
          (ledger.postingsOf(id).in(step._1).isEmpty ||
            ledger.postingsOf(id).in(step._2) === ledger.postingsOf(id).in(step._1))))))

  /** What a call takes of the other calls, of a payment: they leave it decided as it was if it was decided, and
    * posted if it was posted.
    */
  private def undisturbed(id: Term[PaymentId], before: handler.State, after: handler.State)(using Stating)
      : Term[Boolean] =
    (limits.decided(id).in(before) implies (limits.decided(id).in(after) &&
      (limits.approved(id).in(after) === limits.approved(id).in(before)))) &&
      (ledger.posted(id).in(before) implies ledger.posted(id).in(after))

  val everyStepLeavesOthersUndisturbed = Node.claim("Each step of handling a payment leaves every payment " +
      "decided as it was if it was decided, and posted if it was posted: what a call takes of the others.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      handler.handle(p).amongOthers(run => run.steps.forall(step => undisturbed(id, step._1, step._2)))))

  // A crash: the call stopped after any of its steps.

  val neverCommitsAhead = Node.claim("No step of handling a payment moves the committed offset but one that " +
      "leaves the payment applied, when the other calls leave it undisturbed: a crash after any step loses no " +
      "payment.")(
    forall((p: Term[Payment]) =>
      handler.handle(p).amongOthers(run =>
        run.others.forall(move => undisturbed(p.id, move._1, move._2)) implies
          run.steps.forall(step =>
            offsets.committed.in(step._2) === offsets.committed.in(step._1) || applied(p.id, step._2)))))

/** The handler over card limits, a ledger and the consumer's offsets. It has the payment authorised, posts it if
  * it is approved, and only then commits its offset. Each step can be repeated, so a payment delivered again, to
  * this instance after a crash or to another after a rebalance, is applied once.
  */
final class StreamPaymentHandler(limits: CardLimits^, ledger: Ledger^, offsets: ConsumerOffsets^)
    extends PaymentHandler:
  update def handle(payment: Payment): Boolean =
    val approved = limits.authorise(payment)
    if approved then ledger.post(payment)
    offsets.commit(payment.offset)
    approved
