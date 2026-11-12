package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The ledger: the store the payments service keeps the books in. Each method is one transaction of its database;
  * a method that changes the books is an `update`.
  */
final class Ledger(var books: Books) extends Mutable:
  /** Claims an order's payment for the caller: whether it was free. Of two calls claiming one, one is told no. */
  update def claim(order: String): Boolean =
    val fresh = !books.claimed.contains(order)
    if fresh then books = books.copy(claimed = order :: books.claimed)
    fresh

  /** Moves an order's amount from its customer to the shop if the customer's balance covers it: whether it did. */
  update def chargeIfCovered(o: Order): Boolean =
    val covered = o.amount <= Books.balance(books.postings, o.customer)
    if covered then books = books.copy(postings = books.postings ++
      List(Posting(o.id, o.customer, -o.amount), Posting(o.id, "shop", o.amount)))
    covered

object Ledger:
  val claim = Declaration[(Books, String) -> (Boolean, Books)]("claiming an order's payment: whether it was " +
    "free, and the books after")
  val chargeIfCovered = Declaration[(Books, Order) -> (Boolean, Books)]("moving an order's amount to the shop if " +
    "its customer can cover it: whether it did, and the books after")

  val claimCode = updating { (ledger: Ledger^, order: String) => ledger.claim(order) }
  val chargeIfCoveredCode = updating { (ledger: Ledger^, o: Order) => ledger.chargeIfCovered(o) }

  // The ledger's contracts: what each transaction promises, whatever the books it starts from.

  val claimKeepsPostings = Node.claim("Claiming a payment leaves the postings as they are.")(
    forall((books: Term[Books], order: Term[String]) => claim(books, order)._2.postings === books.postings))

  val claimIsWonOnce = Node.claim("A payment's claim is won exactly when it was not claimed before.")(
    forall((books: Term[Books], order: Term[String]) =>
      claim(books, order)._1 === !books.claimed.contains(order)))

  val claimedStaysClaimed = Node.claim("After a claim the payment is claimed, and so is every one claimed before.")(
    forall((books: Term[Books], order: Term[String], other: Term[String]) =>
      (other === order || books.claimed.contains(other)) implies
        claim(books, order)._2.claimed.contains(other)))

  val chargeIsMadeWhenCovered = Node.claim("An order is charged exactly when its customer's balance covers it.")(
    forall((books: Term[Books], o: Term[Order]) =>
      chargeIfCovered(books, o)._1 === (o.amount <= Books.balance(books.postings, o.customer))))

  val chargeKeepsSolvent = Node.claim("Charging an order if covered leaves solvent books solvent.")(
    forall((books: Term[Books], o: Term[Order]) =>
      Books.solvent(books) implies Books.solvent(chargeIfCovered(books, o)._2)))

  val chargeKeepsClaims = Node.claim("Charging an order leaves the claims as they are.")(
    forall((books: Term[Books], o: Term[Order]) => chargeIfCovered(books, o)._2.claimed === books.claimed))

  val chargePostsItsOrder = Node.claim("Charging an order makes postings of that order only.")(
    forall((books: Term[Books], other: Term[String], o: Term[Order]) =>
      (other =!= o.id) implies
        (Books.made(chargeIfCovered(books, o)._2.postings, other) === Books.made(books.postings, other))))

  val chargeMovesTheAmount = Node.claim("A charge made takes the amount from the customer and gives it to the " +
      "shop; every other account has what it had.")(
    forall((books: Term[Books], account: Term[String], o: Term[Order]) =>
      chargeIfCovered(books, o)._1 implies
        (Books.balance(chargeIfCovered(books, o)._2.postings, account) ===
          Books.balance(books.postings, account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val uncoveredChargeChangesNothing = Node.claim("A charge that is not made leaves the books as they are.")(
    forall((books: Term[Books], o: Term[Order]) =>
      !chargeIfCovered(books, o)._1 implies (chargeIfCovered(books, o)._2 === books)))
