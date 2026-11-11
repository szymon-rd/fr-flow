package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The payments service: it claims the order's payment, so that an order charged twice, or twice at once, is
  * charged by one call; then it moves the money if the customer can cover it. Two transactions of the ledger.
  */
final class Payments(ledger: Ledger^):
  def charge(o: Order): Charged =
    val mine = ledger.claim(o.id)
    if !mine then Charged.Duplicate
    else
      val paid = ledger.chargeIfCovered(o)
      if paid then Charged.Done else Charged.Refused

object Payments:
  val charge = Definition[(Books, Order) -> (Charged, Books)]("charging an order: its answer, and the books " +
    "after")

  val chargeCode = updating { (payments: Payments^, o: Order) => payments.charge(o) }

  // The payments' contracts: what the checkout knows of it.

  val chargedWhenCovered = Node.claim("A payment not yet claimed that the customer can cover is done.")(
    forall((books: Term[Books], o: Term[Order]) =>
      (!books.claimed.contains(o.id) && o.amount <= Books.balance(books.postings, o.customer)) implies
        (charge(books, o)._1 === Charged.Done)))

  val doneChargePays = Node.claim("A charge done takes the amount from the customer and gives it to the shop; " +
      "every other account has what it had.")(
    forall((books: Term[Books], account: Term[String], o: Term[Order]) =>
      (charge(books, o)._1 === Charged.Done) implies
        (Books.balance(charge(books, o)._2.postings, account) ===
          Books.balance(books.postings, account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val failedChargeMovesNothing = Node.claim("A charge that is not done makes no posting.")(
    forall((books: Term[Books], o: Term[Order]) =>
      (charge(books, o)._1 =!= Charged.Done) implies (charge(books, o)._2.postings === books.postings)))
