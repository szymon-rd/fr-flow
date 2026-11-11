package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The limits service: it authorises a payment against its card's limit of the day. */
final class Limits(log: SpendLog^):
  def authorise(p: Payment): Boolean = log.assess(p)

object Limits:
  val authorise = Definition[(Spending, Payment) -> (Boolean, Spending)]("authorising a payment: whether it is " +
    "approved, and the spending after")

  val authoriseCode = updating { (limits: Limits^, p: Payment) => limits.authorise(p) }

  val authorisedIsRecorded = Node.claim("A payment authorised is decided, and the answer is the decision " +
      "recorded.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      Spending.decided(authorise(spending, p)._2, p.id) &&
        (authorise(spending, p)._1 === Spending.approved(authorise(spending, p)._2, p.id))))

  val authoriseIsRepeatable = Node.claim("Authorising a payment again gives the answer it got and changes " +
      "nothing.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      authorise(authorise(spending, p)._2, p) === authorise(spending, p)))

  val fittingIsAuthorised = Node.claim("A payment not yet decided that fits the card's limit of its day is " +
      "authorised.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      (!Spending.decided(spending, p.id) &&
        Spending.spent(spending.decisions, p.card, p.day) + p.amount <= spending.limit) implies
        authorise(spending, p)._1))
