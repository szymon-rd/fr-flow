package wallet

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The transfer service: it claims the request, so that a request sent twice, or twice at once, is carried out by
  * one call; then it moves the money if the payer can cover it. Two transactions of the ledger, with other calls
  * free to run between them.
  */
final class Transfers(ledger: Ledger^):
  def transfer(t: Transfer): Outcome =
    val mine = ledger.claim(t.request)
    if !mine then Outcome.Duplicate
    else
      val moved = ledger.moveIfCovered(t)
      if moved then Outcome.Done else Outcome.Refused

object Transfers:
  /** What other calls may do between two steps of a transfer: leave its request undisturbed. */
  val others = lifted { (t: Transfer, before: Books, after: Books) => undisturbed(t.request, before, after) }

  /** A transfer alone, as the statements speak of it: from the books, its answer with the books after it. */
  val transfer = Declaration[(Books, Transfer) -> (Outcome, Books)]("a transfer, alone: its answer, and the books " +
    "after")

  /** A transfer among other calls: from the books and what the others leave before each of its steps (`between`,
    * by the step's number), its answer with every step it took: the books the step started from and those it left.
    */
  val transferAmongOthers = Declaration[(Books, Map[BigInt, Books], Transfer) -> (Outcome, List[(Books, Books)])](
    "a transfer among other calls: its answer, and each of its steps")

  /** The method `transfer`, read both ways: what each Definition above is. */
  val transferCode = updating { (service: Transfers^, t: Transfer) => service.transfer(t) }
  val transferAmongOthersCode = interleaving { (service: Transfers^, t: Transfer) => service.transfer(t) }(others)

  // The service's contracts among other calls: each holds of every step, whatever the others do between steps.

  val neverOverdrawn = Node.claim("A transfer leaves no account overdrawn at any of its steps, whatever other " +
      "calls do between them.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], t: Term[Transfer]) =>
      Books.solvent(books) implies
        transferAmongOthers(books, between, t)._2.forall(step => Books.solvent(step._2))))

  val moneyIsConserved = Node.claim("A transfer makes no money and destroys none, at any of its steps.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], t: Term[Transfer]) =>
      transferAmongOthers(books, between, t)._2.forall(step =>
        Books.total(step._2.postings) === Books.total(step._1.postings))))

  val carriedOutOnce = Node.claim("No step of a transfer adds to the postings of a request already made, " +
      "whatever other calls do between its steps.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], request: Term[String], t: Term[Transfer]) =>
      Books.orderly(books) implies transferAmongOthers(books, between, t)._2.forall(step =>
        Books.made(step._1.postings, request).isEmpty ||
          Books.made(step._2.postings, request) === Books.made(step._1.postings, request))))

  // What the service grants other calls: what it relies on of them (`others`), each of its own steps keeps.

  val leavesOthersUndisturbed = Node.claim("Each step of a transfer leaves every other request undisturbed: the " +
      "books solvent and orderly, no claim undone, no posting of another request made.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], other: Term[String], t: Term[Transfer]) =>
      (Books.solvent(books) && Books.orderly(books) && (other =!= t.request)) implies
        transferAmongOthers(books, between, t)._2.forall(step => undisturbed(other, step._1, step._2))))

  val postsOnlyOnceClaimed = Node.claim("A transfer that finds its request claimed makes no posting, whatever " +
      "other calls do between its steps.")(
    forall((books: Term[Books], between: Term[Map[BigInt, Books]], t: Term[Transfer]) =>
      books.claimed.contains(t.request) implies
        transferAmongOthers(books, between, t)._2.forall(step => step._2.postings === step._1.postings)))

  // The service's contracts alone: what a caller gets.

  val coveredIsDone = Node.claim("Alone, a transfer of a request not yet claimed that its payer can cover is " +
      "done.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      (!books.claimed.contains(t.request) && t.amount <= Books.balance(books.postings, t.from)) implies
        (transfer(books, t)._1 === Outcome.Done)))

  val sentAgainIsDuplicate = Node.claim("Alone, a transfer sent again is answered as a duplicate.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      transfer(transfer(books, t)._2, t)._1 === Outcome.Duplicate))

  val sentAgainChangesNothing = Node.claim("Alone, a transfer sent again leaves the books as the first left them.")(
    forall((books: Term[Books], t: Term[Transfer]) =>
      transfer(transfer(books, t)._2, t)._2 === transfer(books, t)._2))
