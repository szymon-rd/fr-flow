package payments

import frflow.*

// The stream's words: the payments it reads from the log, what its stores keep, and what is said of them. Plain
// Scala, read by FrFlow (`lifted`): the same functions run in production and are what Lean proves things of.

/** A card payment as the log delivers it: its place in the log (`offset`), the id its sender gave it, the card it
  * charges, the merchant it pays, its amount, and the day it counts toward. The log may deliver a payment again
  * (the same offset), and a sender that heard nothing may have sent it twice (another offset, the same id).
  */
final case class Payment(offset: BigInt, id: String, card: String, merchant: String, amount: BigInt, day: BigInt)

object Payment:
  /** The amount is positive: the gateway refuses any other before it reaches the log. */
  given FrSpec[Payment] = FrSpec.derived[Payment].where(p => BigInt(0) < p.amount)

/** What was decided of a payment: approved, or declined for the card's limit on that day. */
final case class Decision(id: String, card: String, day: BigInt, amount: BigInt, approved: Boolean) derives FrSpec

/** The limits' record: what a card may spend in a day, and every decision made, oldest first. */
final case class Spending(limit: BigInt, decisions: List[Decision]) derives FrSpec

object Spending:
  /** Whether a payment was decided, and whether it was approved. */
  val decided = lifted { (spending: Spending, id: String) => spending.decisions.exists(d => d.id == id) }
  val approved = lifted { (spending: Spending, id: String) =>
    spending.decisions.exists(d => d.id == id && d.approved) }

  /** What a card has spent on a day: the sum of its approved payments of that day. */
  val spent = lifted { (decisions: List[Decision], card: String, day: BigInt) =>
    decisions.filter(d => d.approved && d.card == card && d.day == day)
      .foldLeft(BigInt(0))((sum, d) => sum + d.amount) }

  /** No card has spent more than the limit on any day. */
  val withinLimits = lifted { (spending: Spending) =>
    spending.decisions.forall(d => !d.approved || spent(spending.decisions, d.card, d.day) <= spending.limit) }

/** One side of a payment: an account's balance changed by an amount (negative: charged). */
final case class Posting(payment: String, account: String, amount: BigInt) derives FrSpec

/** The ledger's books: every posting made, oldest first, and the payments posted, newest first. */
final case class Books(postings: List[Posting], posted: List[String]) derives FrSpec

object Books:
  /** All the money in the books: the sum of every posting. */
  val total = lifted { (postings: List[Posting]) => postings.foldLeft(BigInt(0))((sum, x) => sum + x.amount) }

  /** The postings made for a payment. */
  val made = lifted { (postings: List[Posting], id: String) => postings.filter(x => x.payment == id) }

  /** Every posting is of a payment marked as posted. */
  val orderly = lifted { (books: Books) => books.postings.forall(x => books.posted.contains(x.payment)) }

/** Everything the stream keeps: the state the processor works on, one part for each service it holds. The last is
  * the position in the log: the offset of the next payment to handle.
  */
final case class Pipeline(spending: Spending, books: Books, committed: BigInt) derives FrSpec

object Pipeline:
  /** A payment is applied: it was decided, and if it was approved it is posted. */
  val applied = lifted { (pipeline: Pipeline, id: String) =>
    Spending.decided(pipeline.spending, id) &&
      (!Spending.approved(pipeline.spending, id) || pipeline.books.posted.contains(id)) }
