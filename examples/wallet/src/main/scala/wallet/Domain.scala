package wallet

import frflow.*

// The wallet's words: the data its services and its ledger speak in, and what is said of the books. Plain Scala,
// read by FrFlow (`lifted`): the same functions run in production and are what Lean proves things of.

/** One side of a movement of money: an account's balance changed by an amount (negative: taken), for a request. */
final case class Posting(request: String, account: String, amount: BigInt) derives FrSpec

/** The ledger's books: every posting made, oldest first, and the requests claimed, newest first. */
final case class Books(postings: List[Posting], claimed: List[String]) derives FrSpec

/** A transfer asked for: an amount from one account to another, under the name its sender gave the request. A
  * sender that hears nothing sends the request again under the same name.
  */
final case class Transfer(request: String, from: String, to: String, amount: BigInt)

object Transfer:
  /** The amount is positive: the API refuses any other before a service sees it. */
  given FrSpec[Transfer] = FrSpec.derived[Transfer].where(t => BigInt(0) < t.amount)

/** What a transfer is answered: done, refused (the payer cannot cover it), or a duplicate of a request claimed. */
enum Outcome derives FrSpec:
  case Done, Refused, Duplicate

object Books:
  /** An account's balance: the sum of its postings. */
  val balance = lifted { (postings: List[Posting], account: String) =>
    postings.filter(p => p.account == account).foldLeft(BigInt(0))((sum, p) => sum + p.amount) }

  /** All the money in the books: the sum of every posting. */
  val total = lifted { (postings: List[Posting]) => postings.foldLeft(BigInt(0))((sum, p) => sum + p.amount) }

  /** The postings made for a request. */
  val made = lifted { (postings: List[Posting], request: String) => postings.filter(p => p.request == request) }

  /** No account is overdrawn. */
  val solvent = lifted { (books: Books) =>
    books.postings.forall(p => BigInt(0) <= balance(books.postings, p.account)) }

  /** Every posting is of a request that was claimed. */
  val orderly = lifted { (books: Books) => books.postings.forall(p => books.claimed.contains(p.request)) }
