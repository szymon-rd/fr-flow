package shop

import frflow.*

// The shop's words: the data its stores keep and its services speak in, and what is said of it. Plain Scala, read
// by FrFlow (`lifted`): the same functions run in production and are what Lean proves things of.

/** One side of a payment: an account's balance changed by an amount (negative: taken), for an order. */
final case class Posting(order: String, account: String, amount: BigInt) derives FrSpec

/** The ledger's books: every posting made, oldest first, and the orders whose payment was claimed, newest first. */
final case class Books(postings: List[Posting], claimed: List[String]) derives FrSpec

object Books:
  /** An account's balance: the sum of its postings. */
  val balance = lifted { (postings: List[Posting], account: String) =>
    postings.filter(p => p.account == account).foldLeft(BigInt(0))((sum, p) => sum + p.amount) }

  /** The postings made for an order. */
  val made = lifted { (postings: List[Posting], order: String) => postings.filter(p => p.order == order) }

  /** No account is overdrawn. */
  val solvent = lifted { (books: Books) =>
    books.postings.forall(p => BigInt(0) <= balance(books.postings, p.account)) }

  /** Every posting is of an order whose payment was claimed. */
  val orderly = lifted { (books: Books) => books.postings.forall(p => books.claimed.contains(p.order)) }

/** Units of a product entering what the warehouse has to sell (a delivery, a hold put back) or leaving it
  * (negative: held for an order).
  */
final case class Movement(order: String, sku: String, units: BigInt) derives FrSpec

/** The warehouse's stock: every movement, oldest first. */
final case class Stock(movements: List[Movement]) derives FrSpec

object Stock:
  /** The units of a product the warehouse has to sell: the sum of its movements. */
  val available = lifted { (movements: List[Movement], sku: String) =>
    movements.filter(m => m.sku == sku).foldLeft(BigInt(0))((sum, m) => sum + m.units) }

  /** No product is oversold: none has fewer than no units to sell. */
  val stocked = lifted { (stock: Stock) =>
    stock.movements.forall(m => BigInt(0) <= available(stock.movements, m.sku)) }

/** How an order ended. */
enum Status derives FrSpec:
  case Confirmed, Rejected

/** An order's end, as the journal records it. */
final case class Settlement(order: String, status: Status) derives FrSpec

/** The checkout's journal: the orders registered, newest first, and how each ended, oldest first. */
final case class Journal(registered: List[String], settled: List[Settlement]) derives FrSpec

object Journal:
  /** Whether an order is recorded as confirmed. */
  val confirmed = lifted { (journal: Journal, order: String) =>
    journal.settled.contains(Settlement(order, Status.Confirmed)) }

/** An order: units of one product for a customer, for an amount, under the id its sender gave it. A sender that
  * hears nothing sends the order again under the same id.
  */
final case class Order(id: String, customer: String, sku: String, units: BigInt, amount: BigInt)

object Order:
  /** At least one unit, for a positive amount: the API refuses any other before a service sees it. */
  given FrSpec[Order] = FrSpec.derived[Order].where(o => BigInt(0) < o.units && BigInt(0) < o.amount)

/** What a charge is answered: done, refused (the customer cannot cover it), or a duplicate of one claimed. */
enum Charged derives FrSpec:
  case Done, Refused, Duplicate

/** What placing an order is answered. */
enum Placement derives FrSpec:
  case Confirmed, OutOfStock, PaymentRefused, Duplicate

/** Everything the shop keeps: the state the checkout works on, one part for each port it holds. */
final case class ShopState(stock: Stock, books: Books, journal: Journal) derives FrSpec
