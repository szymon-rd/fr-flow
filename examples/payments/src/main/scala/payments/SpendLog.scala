package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The spend log: the store the limits service keeps its decisions in. Each method is one transaction. */
final class SpendLog(var spending: Spending) extends Mutable:
  /** Decides a payment not yet decided, approving it if the card's spending of that day with it stays within the
    * limit, and records the decision; a payment already decided is left as it was. Answers what is recorded.
    */
  update def assess(p: Payment): Boolean =
    val fits = Spending.spent(spending.decisions, p.card, p.day) + p.amount <= spending.limit
    if !Spending.decided(spending, p.id) then
      spending = spending.copy(decisions = spending.decisions :+ Decision(p.id, p.card, p.day, p.amount, fits))
    Spending.approved(spending, p.id)

  /** Whether a payment fits its card's limit of the day, and a decision recorded as given: the two halves of
    * `assess`, each a transaction of its own (`Hasty`).
    */
  def fits(p: Payment): Boolean = Spending.spent(spending.decisions, p.card, p.day) + p.amount <= spending.limit
  update def record(d: Decision): Unit = spending = spending.copy(decisions = spending.decisions :+ d)

object SpendLog:
  val assess = Definition[(Spending, Payment) -> (Boolean, Spending)]("deciding a payment against its card's " +
    "limit: whether it is approved, and the spending after")

  val assessCode = updating { (log: SpendLog^, p: Payment) => log.assess(p) }

  // The spend log's contracts.

  val assessAnswersWhatIsRecorded = Node.claim("A payment assessed is decided, and the answer is the decision " +
      "recorded.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      Spending.decided(assess(spending, p)._2, p.id) &&
        (assess(spending, p)._1 === Spending.approved(assess(spending, p)._2, p.id))))

  val assessKeepsWithinLimits = Node.claim("Assessing a payment leaves no card over its limit.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      Spending.withinLimits(spending) implies Spending.withinLimits(assess(spending, p)._2)))

  val assessKeepsDecisions = Node.claim("Assessing a payment leaves every payment decided before decided as it " +
      "was.")(
    forall((spending: Term[Spending], id: Term[String], p: Term[Payment]) =>
      Spending.decided(spending, id) implies
        (Spending.decided(assess(spending, p)._2, id) &&
          (Spending.approved(assess(spending, p)._2, id) === Spending.approved(spending, id)))))

  val decidedIsNotAssessedAgain = Node.claim("Assessing a payment already decided changes nothing.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      Spending.decided(spending, p.id) implies (assess(spending, p)._2 === spending)))

  val fittingPassesAssessment = Node.claim("A payment not yet decided that fits the card's limit of its day is " +
      "approved.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      (!Spending.decided(spending, p.id) &&
        Spending.spent(spending.decisions, p.card, p.day) + p.amount <= spending.limit) implies
        assess(spending, p)._1))
