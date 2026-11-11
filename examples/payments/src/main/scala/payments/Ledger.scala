package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The ledger: the store the accounts service keeps the books in. Each method is one transaction. */
final class Ledger(var books: Books) extends Mutable:
  /** Posts a payment's two sides and marks it posted, unless it is marked already: the mark and the postings are
    * made in one transaction, so a payment is never marked without its postings, or posted without its mark.
    */
  update def postOnce(p: Payment): Unit =
    if !books.posted.contains(p.id) then
      books = Books(books.postings ++ List(Posting(p.id, p.card, -p.amount), Posting(p.id, p.merchant, p.amount)),
        p.id :: books.posted)

  /** Posts a payment's two sides and marks it, whatever is marked: what a first version does (`Blind`). */
  update def append(p: Payment): Unit =
    books = Books(books.postings ++ List(Posting(p.id, p.card, -p.amount), Posting(p.id, p.merchant, p.amount)),
      p.id :: books.posted)

object Ledger:
  val postOnce = Definition[(Books, Payment) -> (Unit, Books)]("posting a payment unless it is posted already: " +
    "the books after")

  val postOnceCode = updating { (ledger: Ledger^, p: Payment) => ledger.postOnce(p) }

  // The ledger's contracts.

  val postMarksPosted = Node.claim("A payment posted is marked as posted.")(
    forall((books: Term[Books], p: Term[Payment]) => postOnce(books, p)._2.posted.contains(p.id)))

  val postKeepsTotal = Node.claim("Posting a payment leaves the total of the books as it was.")(
    forall((books: Term[Books], p: Term[Payment]) =>
      Books.total(postOnce(books, p)._2.postings) === Books.total(books.postings)))

  val repostChangesNothing = Node.claim("Posting a payment marked as posted changes nothing.")(
    forall((books: Term[Books], p: Term[Payment]) =>
      books.posted.contains(p.id) implies (postOnce(books, p)._2 === books)))

  val postKeepsPosted = Node.claim("Posting a payment leaves every payment posted before marked as posted.")(
    forall((books: Term[Books], id: Term[String], p: Term[Payment]) =>
      books.posted.contains(id) implies postOnce(books, p)._2.posted.contains(id)))

  val postKeepsOrderly = Node.claim("Posting a payment leaves orderly books orderly.")(
    forall((books: Term[Books], p: Term[Payment]) =>
      Books.orderly(books) implies Books.orderly(postOnce(books, p)._2)))

  val postAddsToNoPayment = Node.claim("Posting a payment adds nothing to the postings of a payment that has " +
      "some, in orderly books.")(
    forall((books: Term[Books], id: Term[String], p: Term[Payment]) =>
      Books.orderly(books) implies (Books.made(books.postings, id).isEmpty ||
        Books.made(postOnce(books, p)._2.postings, id) === Books.made(books.postings, id))))
