package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The limits service: it decides each payment against its card's limit of the day, once. */
trait Limits extends Mutable:
  /** Decides a payment not yet decided, and answers what is decided of it: whether it is approved. */
  update def authorise(p: Payment): Boolean
  def decided(id: String): Boolean
  def approved(id: String): Boolean
  /** What a card has spent on a day: the sum of its approved payments of that day. */
  def spent(card: String, day: BigInt): BigInt
  /** What a card may spend in a day. */
  def limit: BigInt

object Limits:
  val limits = Definition[Limits]("the limits service: it decides each payment against its card's limit of the day")

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
      (!limits.decided(p.id) && limits.spent(p.card, p.day) + p.amount <= limits.limit) implies
        limits.authorise(p).result))

  val authoriseKeepsWithinLimit = Node.claim("Authorising a payment leaves a card within its limit of a day " +
      "within it.")(
    forall((card: Term[String], day: Term[BigInt], p: Term[Payment]) =>
      (limits.spent(card, day) <= limits.limit) implies
        (limits.spent(card, day).in(limits.authorise(p).after) <= limits.limit.in(limits.authorise(p).after))))

  val authoriseKeepsDecisions = Node.claim("Authorising a payment leaves every payment decided before decided " +
      "as it was.")(
    forall((id: Term[String], p: Term[Payment]) =>
      limits.decided(id) implies
        (limits.decided(id).in(limits.authorise(p).after) &&
          (limits.approved(id).in(limits.authorise(p).after) === limits.approved(id)))))

/** The limits service over a list of decisions. */
final class SpendLimits(val limit: BigInt, var decisions: List[Decision]) extends Limits:
  update def authorise(p: Payment): Boolean =
    val fits = spent(p.card, p.day) + p.amount <= limit
    if !decided(p.id) then decisions = decisions :+ Decision(p.id, p.card, p.day, p.amount, fits)
    approved(p.id)

  def decided(id: String): Boolean = decisions.exists(d => d.id == id)
  def approved(id: String): Boolean = decisions.exists(d => d.id == id && d.approved)
  def spent(card: String, day: BigInt): BigInt =
    decisions.filter(d => d.approved && d.card == card && d.day == day).foldLeft(BigInt(0))((sum, d) => sum + d.amount)
