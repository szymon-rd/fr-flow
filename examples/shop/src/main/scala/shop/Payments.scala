package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The payments service: it charges an order to its customer, once. */
trait Payments extends Mutable:
  /** Charges an order: done, refused (the customer cannot cover it), or a duplicate of a payment claimed. */
  update def charge(o: Order): Charged
  /** Whether an order's payment was claimed. */
  def claimed(order: String): Boolean
  /** An account's balance. */
  def balance(account: String): BigInt

/** What the checkout knows of the payments. */
object Payments:
  val payments = Declaration[Payments]("the payments service: it charges an order to its customer, once")

  val chargedWhenCovered = Node.claim("A payment not yet claimed that the customer can cover is done.")(
    forall((o: Term[Order]) =>
      (!payments.claimed(o.id) && o.amount <= payments.balance(o.customer)) implies
        (payments.charge(o).result === Charged.Done)))

  val doneChargePays = Node.claim("A charge done takes the amount from the customer and gives it to the shop; " +
      "every other account has what it had.")(
    forall((account: Term[String], o: Term[Order]) =>
      (payments.charge(o).result === Charged.Done) implies
        (payments.balance(account).in(payments.charge(o).after) ===
          payments.balance(account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val failedChargeMovesNothing = Node.claim("A charge that is not done leaves every balance as it was.")(
    forall((account: Term[String], o: Term[Order]) =>
      (payments.charge(o).result =!= Charged.Done) implies
        (payments.balance(account).in(payments.charge(o).after) === payments.balance(account))))

/** The payments over a ledger: it claims the order's payment, so that an order charged twice, or twice at once,
  * is charged by one call; then it moves the money if the customer can cover it. Two transactions of the ledger.
  */
final class LedgerPayments(ledger: Ledger^) extends Payments:
  update def charge(o: Order): Charged =
    val mine = ledger.claim(o.id)
    if !mine then Charged.Duplicate
    else
      val paid = ledger.chargeIfCovered(o)
      if paid then Charged.Done else Charged.Refused

  def claimed(order: String): Boolean = ledger.claimed(order)
  def balance(account: String): BigInt = ledger.balance(account)
