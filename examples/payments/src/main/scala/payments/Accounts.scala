package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import frflow.*

/** The accounts service: it posts a payment to the books, once. */
final class Accounts(ledger: Ledger^):
  def post(p: Payment): Unit = ledger.postOnce(p)

object Accounts:
  val post = Definition[(Books, Payment) -> (Unit, Books)]("posting a payment: the books after")

  val postCode = updating { (accounts: Accounts^, p: Payment) => accounts.post(p) }

  val postedIsMarked = Node.claim("A payment posted to the accounts is marked as posted.")(
    forall((books: Term[Books], p: Term[Payment]) => post(books, p)._2.posted.contains(p.id)))

  val postIsRepeatable = Node.claim("Posting a payment again changes nothing.")(
    forall((books: Term[Books], p: Term[Payment]) => post(post(books, p)._2, p)._2 === post(books, p)._2))
