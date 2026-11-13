package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*
import Ledger.ledger

/** The payments service: it charges an order to its customer, once. */
trait Payments extends Mutable:
  /** Charges an order: done, refused (the customer cannot cover it), or a duplicate of a payment claimed. */
  update def charge(o: Order): Charged

/** What the checkout knows of the payments, said of the ledger the payments hold. */
object Payments:
  val payments = Declaration[Payments]("the payments service: it charges an order to its customer, once")

  val chargedWhenCovered = Node.claim("A payment not yet claimed that the customer can cover is done.")(
    forall((o: Term[Order]) =>
      (!ledger.claimed(o.id) && o.amount <= ledger.balance(o.customer)) implies
        (payments.charge(o).result === Charged.Done)))

  val doneChargePays = Node.claim("A charge done takes the amount from the customer and gives it to the shop; " +
      "every other account has what it had.")(
    forall((account: Term[String], o: Term[Order]) =>
      (payments.charge(o).result === Charged.Done) implies
        (ledger.balance(account).in(payments.charge(o).after) ===
          ledger.balance(account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val failedChargeMovesNothing = Node.claim("A charge that is not done leaves every balance as it was.")(
    forall((account: Term[String], o: Term[Order]) =>
      (payments.charge(o).result =!= Charged.Done) implies
        (ledger.balance(account).in(payments.charge(o).after) === ledger.balance(account))))

  val chargeLeavesSolvent = Node.claim("Charging an order leaves an account that is not overdrawn not overdrawn.")(
    forall((account: Term[String], o: Term[Order]) =>
      (ledger.balance(account) >= 0) implies (ledger.balance(account).in(payments.charge(o).after) >= 0)))

  // What the checkout takes of the payments for an order charged once, and for every other order's sake.

  val chargePostsOnce = Node.claim("Charging an order makes no posting of another order, nor of an order whose " +
      "payment is already claimed.")(
    forall((order: Term[String], o: Term[Order]) =>
      (order =!= o.id || ledger.claimed(order)) implies
        (ledger.postingsOf(order).in(payments.charge(o).after) === ledger.postingsOf(order))))

  val chargeKeepsClaimed = Node.claim("Charging an order leaves every payment claimed that was.")(
    forall((order: Term[String], o: Term[Order]) =>
      ledger.claimed(order) implies ledger.claimed(order).in(payments.charge(o).after)))

  val chargeKeepsOrderly = Node.claim("Charging an order leaves the books orderly about every order: one with " +
      "postings has its payment claimed.")(
    forall((order: Term[String], o: Term[Order]) =>
      (ledger.postingsOf(order).isEmpty || ledger.claimed(order)) implies
        (ledger.postingsOf(order).in(payments.charge(o).after).isEmpty ||
          ledger.claimed(order).in(payments.charge(o).after))))

  // Between the two transactions of one charge: what a charge takes of the other calls, and what it then keeps.

  val noChargeStepPostsForAnother = Node.claim("No step of charging an order makes a posting of another order, " +
      "or undoes the claim of a payment, whatever other calls do between the steps.")(
    forall((other: Term[String], o: Term[Order]) =>
      payments.charge(o).amongOthers(run => run.steps.forall(step =>
        ((other =!= o.id) implies
          (ledger.postingsOf(other).in(step._2) === ledger.postingsOf(other).in(step._1))) &&
          (ledger.claimed(other).in(step._1) implies ledger.claimed(other).in(step._2))))))

  val chargedOnceAmongOthers = Node.claim("An order whose books are orderly is charged at most once, whatever " +
      "other calls do between the two transactions of its charge, as long as they make no posting of it: no " +
      "step of charging it adds to postings it already has.")(
    forall((o: Term[Order]) =>
      (ledger.postingsOf(o.id).isEmpty || ledger.claimed(o.id)) implies
        payments.charge(o).amongOthers(run =>
          run.others.forall(theirs =>
            ledger.postingsOf(o.id).in(theirs._2) === ledger.postingsOf(o.id).in(theirs._1)) implies
            run.steps.forall(step =>
              !ledger.postingsOf(o.id).in(step._1).isEmpty implies
                (ledger.postingsOf(o.id).in(step._2) === ledger.postingsOf(o.id).in(step._1))))))

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
