package shop

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The ledger: every account's balance, and the orders whose payment was claimed. Each member that changes it is
  * one transaction.
  */
trait Ledger extends Mutable:
  /** Claims an order's payment for the caller: whether it was free. Of two calls claiming one, one is told no. */
  update def claim(order: String): Boolean
  /** Moves an order's amount from its customer to the shop if the customer's balance covers it: whether it did. */
  update def chargeIfCovered(o: Order): Boolean
  /** Whether an order's payment was claimed. */
  def claimed(order: String): Boolean
  /** An account's balance. */
  def balance(account: String): BigInt
  /** The postings made for an order, in the order made: none, or its two sides. */
  def postingsOf(order: String): List[Posting]

object Ledger:
  val ledger = Declaration[Ledger]("the ledger: the accounts' balances, and the payments claimed")

  val claimKeepsBalances = Node.claim("Claiming a payment leaves every balance as it is.")(
    forall((account: Term[String], order: Term[String]) =>
      ledger.balance(account).in(ledger.claim(order).after) === ledger.balance(account)))

  val claimKeepsPostings = Node.claim("Claiming a payment leaves every order's postings as they are.")(
    forall((other: Term[String], order: Term[String]) =>
      ledger.postingsOf(other).in(ledger.claim(order).after) === ledger.postingsOf(other)))

  val claimIsWonOnce = Node.claim("A payment's claim is won exactly when it was not claimed before.")(
    forall((order: Term[String]) => ledger.claim(order).result === !ledger.claimed(order)))

  val claimedStaysClaimed = Node.claim("After a claim the payment is claimed, and so is every one claimed before.")(
    forall((order: Term[String], other: Term[String]) =>
      (other === order || ledger.claimed(other)) implies ledger.claimed(other).in(ledger.claim(order).after)))

  val chargeIsMadeWhenCovered = Node.claim("An order is charged exactly when its customer's balance covers it.")(
    forall((o: Term[Order]) => ledger.chargeIfCovered(o).result === (o.amount <= ledger.balance(o.customer))))

  val chargeKeepsSolvent = Node.claim("Charging an order if covered leaves an account that is not overdrawn " +
      "not overdrawn.")(
    forall((account: Term[String], o: Term[Order]) =>
      (ledger.balance(account) >= 0) implies (ledger.balance(account).in(ledger.chargeIfCovered(o).after) >= 0)))

  val chargeKeepsClaims = Node.claim("Charging an order leaves the claims as they are.")(
    forall((order: Term[String], o: Term[Order]) =>
      ledger.claimed(order).in(ledger.chargeIfCovered(o).after) === ledger.claimed(order)))

  val chargePostsItsOrder = Node.claim("Charging an order makes postings of that order only.")(
    forall((other: Term[String], o: Term[Order]) =>
      (other =!= o.id) implies
        (ledger.postingsOf(other).in(ledger.chargeIfCovered(o).after) === ledger.postingsOf(other))))

  val chargeMovesTheAmount = Node.claim("A charge made takes the amount from the customer and gives it to the " +
      "shop; every other account has what it had.")(
    forall((account: Term[String], o: Term[Order]) =>
      ledger.chargeIfCovered(o).result implies
        (ledger.balance(account).in(ledger.chargeIfCovered(o).after) ===
          ledger.balance(account) + when(account === "shop")(o.amount).otherwise(0) -
            when(account === o.customer)(o.amount).otherwise(0))))

  val uncoveredChargeChangesNothing = Node.claim("A charge that is not made leaves the ledger as it is.")(
    forall((o: Term[Order]) =>
      !ledger.chargeIfCovered(o).result implies (ledger.chargeIfCovered(o).after === ledger.current)))

/** The ledger kept as every posting made, oldest first, and the orders whose payment was claimed, newest first. */
final class PostingLedger(var postings: List[Posting], var claims: List[String]) extends Ledger:
  update def claim(order: String): Boolean =
    val fresh = !claimed(order)
    if fresh then claims = order :: claims
    fresh

  update def chargeIfCovered(o: Order): Boolean =
    val covered = o.amount <= balance(o.customer)
    if covered then
      postings = postings ++ List(Posting(o.id, o.customer, -o.amount), Posting(o.id, "shop", o.amount))
    covered

  def claimed(order: String): Boolean = claims.contains(order)
  def balance(account: String): BigInt =
    postings.filter(p => p.account == account).foldLeft(BigInt(0))((sum, p) => sum + p.amount)
  def postingsOf(order: String): List[Posting] = postings.filter(p => p.order == order)
