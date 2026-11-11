package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The limits service written check-then-act: it looks whether the payment fits, and then records what it saw.
  * Alone it leaves no card over its limit (`hastyKeepsLimitsAlone`, proven). Among other calls, what it saw may
  * no longer hold when it records it: two instances each approve a payment that fits alone, and the card is over
  * its limit (`PaymentsExamples`). `Processor.neverOverTheLimit` cannot be proven over it.
  */
final class Hasty(log: SpendLog^):
  def authorise(p: Payment): Boolean =
    val fits = log.fits(p)
    log.record(Decision(p.id, p.card, p.day, p.amount, fits))
    fits

object Hasty:
  /** What other calls may do to the spending between the two steps: leave no card over its limit, the limit as
    * it is, and a payment decided decided.
    */
  val keepLimits = lifted { (p: Payment, before: Spending, after: Spending) =>
    Spending.withinLimits(after) && after.limit == before.limit &&
      (!Spending.decided(before, p.id) || Spending.decided(after, p.id)) }

  val hastyAuthorise = Definition[(Spending, Payment) -> (Boolean, Spending)]("the hasty limits authorising a " +
    "payment, alone: whether it is approved, and the spending after")
  val hastyAmongOthers =
    Definition[(Spending, Map[BigInt, Spending], Payment) -> (Boolean, List[(Spending, Spending)])](
      "the hasty limits authorising a payment among other calls: its answer, and each of its steps")

  val hastyCode = updating { (hasty: Hasty^, p: Payment) => hasty.authorise(p) }
  val hastyAmongOthersCode = interleaving { (hasty: Hasty^, p: Payment) => hasty.authorise(p) }(keepLimits)

  val hastyKeepsLimitsAlone = Node.claim("Alone, the hasty limits leave no card over its limit.")(
    forall((spending: Term[Spending], p: Term[Payment]) =>
      Spending.withinLimits(spending) implies Spending.withinLimits(hastyAuthorise(spending, p)._2)))

  val hastyRecordsOnce = Node.claim("Among other calls, the hasty limits take one step that changes the " +
      "spending.")(
    forall((spending: Term[Spending], between: Term[Map[BigInt, Spending]], p: Term[Payment]) =>
      !hastyAmongOthers(spending, between, p)._2.isEmpty))
