package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** Card limits: each payment is authorised once, against what its card may spend in a day. */
trait CardLimits extends Mutable:
  /** Authorises a payment not yet decided, and answers what is decided of it: whether it is approved. */
  update def authorise(payment: Payment): Boolean
  /** Whether a payment has been decided, approved or declined. */
  def decided(id: PaymentId): Boolean
  /** Whether a payment has been decided and approved. */
  def approved(id: PaymentId): Boolean
  /** What a card has spent on a day: the sum of its approved payments of that day. */
  def spent(card: CardId, day: BigInt): BigInt
  /** What a card may spend in a day. */
  def dailyLimit: BigInt

object CardLimits:
  val limits = Declaration[CardLimits]("the card limits: each payment authorised once against its card's limit of " +
    "the day")

  val authorisedIsRecorded = Node.claim("A payment authorised is decided, and the answer is the decision " +
      "recorded.")(
    forall((p: Term[Payment]) =>
      limits.decided(p.id).in(limits.authorise(p).after) &&
        (limits.authorise(p).result === limits.approved(p.id).in(limits.authorise(p).after))))

  val authoriseIsRepeatable = Node.claim("Authorising a payment again gives the answer it got and changes " +
      "nothing.")(
    forall((p: Term[Payment]) =>
      (limits.authorise(p).in(limits.authorise(p).after).result === limits.authorise(p).result) &&
        (limits.authorise(p).in(limits.authorise(p).after).after === limits.authorise(p).after)))

  val fittingIsAuthorised = Node.claim("A payment not yet decided that fits its card's limit of the day is " +
      "authorised.")(
    forall((p: Term[Payment]) =>
      (!limits.decided(p.id) && limits.spent(p.card, p.day) + p.amount <= limits.dailyLimit) implies
        limits.authorise(p).result))

  val authoriseKeepsWithinLimit = Node.claim("Authorising a payment leaves a card within its limit of a day " +
      "within it.")(
    forall((card: Term[CardId], day: Term[BigInt], p: Term[Payment]) =>
      (limits.spent(card, day) <= limits.dailyLimit) implies
        (limits.spent(card, day).in(limits.authorise(p).after) <= limits.dailyLimit.in(limits.authorise(p).after))))

  val authoriseKeepsDecisions = Node.claim("Authorising a payment leaves every payment decided before decided " +
      "as it was.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      limits.decided(id) implies
        (limits.decided(id).in(limits.authorise(p).after) &&
          (limits.approved(id).in(limits.authorise(p).after) === limits.approved(id)))))

/** Card limits kept as the decisions made, in the order made. */
final class RecordedLimits(val dailyLimit: BigInt, var decisions: List[Decision]) extends CardLimits:
  update def authorise(payment: Payment): Boolean =
    val fits = spent(payment.card, payment.day) + payment.amount <= dailyLimit
    if !decided(payment.id) then
      decisions = decisions :+ Decision(payment.id, payment.card, payment.day, payment.amount, fits)
    approved(payment.id)

  def decided(id: PaymentId): Boolean = decisions.exists(d => d.id == id)
  def approved(id: PaymentId): Boolean = decisions.exists(d => d.id == id && d.approved)
  def spent(card: CardId, day: BigInt): BigInt =
    decisions.filter(d => d.approved && d.card == card && d.day == day).foldLeft(BigInt(0))((sum, d) => sum + d.amount)
