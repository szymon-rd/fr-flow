package wallet

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The ledger: the store the wallet's services keep the books in. Each method is one transaction of its database,
  * so other calls see the books before it or after it, never between; a method that changes them is an `update`.
  * This class is the ledger's model, and its implementation where the books fit in memory.
  */
final class Ledger(var books: Books) extends Mutable:
  /** Claims a request for the caller: whether it was free. Of two calls claiming one request, one is told no. */
  update def claim(request: String): Boolean =
    val fresh = !books.claimed.contains(request)
    if fresh then books = books.copy(claimed = request :: books.claimed)
    fresh

  /** Moves a transfer's amount from its payer to its payee if the payer's balance covers it: whether it did. */
  update def moveIfCovered(t: Transfer): Boolean =
    val covered = t.amount <= Books.balance(books.postings, t.from)
    if covered then books = books.copy(postings = books.postings ++
      List(Posting(t.request, t.from, -t.amount), Posting(t.request, t.to, t.amount)))
    covered

  /** Whether a request was claimed, and an account's balance: what a service may read before it decides. */
  def isClaimed(request: String): Boolean = books.claimed.contains(request)
  def balanceOf(account: String): BigInt = Books.balance(books.postings, account)

  /** Marks a request claimed, and moves a transfer's amount, each whatever the books hold. */
  update def mark(request: String): Unit = books = books.copy(claimed = request :: books.claimed)
  update def move(t: Transfer): Unit = books = books.copy(postings = books.postings ++
    List(Posting(t.request, t.from, -t.amount), Posting(t.request, t.to, t.amount)))

object Ledger:
  // The ledger's two transactions the transfer service is made of, as the statements speak of them: from the books,
  // the answer with the books after it. Each is known to the services by its contracts below, and is the code of
  // the method of its name (`claimCode`, `moveIfCoveredCode`: the method's body, read).
  val claim = Definition[(Books, String) -> (Boolean, Books)]("claiming a request: whether it was free, and the " +
    "books after")
  val moveIfCovered = Definition[(Books, Transfer) -> (Boolean, Books)]("moving a transfer's amount if its payer " +
    "can cover it: whether it did, and the books after")

  val claimCode = updating { (ledger: Ledger^, request: String) => ledger.claim(request) }
  val moveIfCoveredCode = updating { (ledger: Ledger^, t: Transfer) => ledger.moveIfCovered(t) }

  // The ledger's contracts: what each transaction promises, whatever the books it starts from.

  val claimKeepsPostings = Node.claim("Claiming a request leaves the postings as they are.")(
    forall((books: Term[Books], request: Term[String]) => claim(books, request)._2.postings === books.postings))

  val claimIsWonOnce = Node.claim("A claim is won exactly when the request was not claimed before.")(
    forall((books: Term[Books], request: Term[String]) =>
      claim(books, request)._1 === !books.claimed.contains(request)))

  val claimedStaysClaimed = Node.claim("After a claim the request is claimed, and so is every request claimed " +
      "before.")(
    forall((books: Term[Books], request: Term[String], other: Term[String]) =>
      (other === request || books.claimed.contains(other)) implies
        claim(books, request)._2.claimed.contains(other)))

  val lostClaimChangesNothing = Node.claim("A claim that is not won leaves the books as they are.")(
    forall((books: Term[Books], request: Term[String]) =>
      !claim(books, request)._1 implies (claim(books, request)._2 === books)))

  val moveIsMadeWhenCovered = Node.claim("Money is moved exactly when the payer's balance covers the amount.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      moveIfCovered(books, t)._1 === (t.amount <= Books.balance(books.postings, t.from))))

  val moveKeepsSolvent = Node.claim("Moving money if covered leaves solvent books solvent.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      Books.solvent(books) implies Books.solvent(moveIfCovered(books, t)._2)))

  val moveKeepsTotal = Node.claim("Moving money leaves the total of the books as it was.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      Books.total(moveIfCovered(books, t)._2.postings) === Books.total(books.postings)))

  val moveKeepsClaims = Node.claim("Moving money leaves the claims as they are.")(
    forall((books: Term[Books], t: Term[Transfer]) => moveIfCovered(books, t)._2.claimed === books.claimed))

  val movePostsItsRequest = Node.claim("Moving money makes postings of the transfer's own request only.")(
    forall((books: Term[Books], other: Term[String], t: Term[Transfer]) =>
      (other =!= t.request) implies
        (Books.made(moveIfCovered(books, t)._2.postings, other) === Books.made(books.postings, other))))
