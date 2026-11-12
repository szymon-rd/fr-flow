package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The accounts service: it posts each payment to the books, once. */
trait Accounts extends Mutable:
  /** Posts a payment's two sides, unless it is posted already. */
  update def post(p: Payment): Unit
  def posted(id: String): Boolean
  def postingsOf(id: String): List[Posting]
  /** All the money in the books: the sum of every posting. */
  def total: BigInt

object Accounts:
  val accounts = Declaration[Accounts]("the accounts service: it posts each payment to the books, once")

  val postedIsMarked = Node.claim("A payment posted is marked as posted.")(
    forall((p: Term[Payment]) => accounts.posted(p.id).in(accounts.post(p).after)))

  val postIsRepeatable = Node.claim("Posting a payment again changes nothing.")(
    forall((p: Term[Payment]) => accounts.post(p).in(accounts.post(p).after).after === accounts.post(p).after))

  val postKeepsTotal = Node.claim("Posting a payment leaves the total of the books as it was.")(
    forall((p: Term[Payment]) => accounts.total.in(accounts.post(p).after) === accounts.total))

  val postKeepsPosted = Node.claim("Posting a payment leaves every payment posted before marked as posted.")(
    forall((id: Term[String], p: Term[Payment]) =>
      accounts.posted(id) implies accounts.posted(id).in(accounts.post(p).after)))

  val postKeepsMarks = Node.claim("Posting a payment leaves a payment that has postings only if it is marked " +
      "so.")(
    forall((id: Term[String], p: Term[Payment]) =>
      (accounts.postingsOf(id).isEmpty || accounts.posted(id)) implies
        (accounts.postingsOf(id).in(accounts.post(p).after).isEmpty || accounts.posted(id).in(accounts.post(p).after))))

  val postAddsToNoPayment = Node.claim("Posting a payment adds nothing to the postings of a payment that has " +
      "some, where a payment with postings is marked.")(
    forall((id: Term[String], p: Term[Payment]) =>
      (accounts.postingsOf(id).isEmpty || accounts.posted(id)) implies
        (accounts.postingsOf(id).isEmpty ||
          accounts.postingsOf(id).in(accounts.post(p).after) === accounts.postingsOf(id))))

/** The accounts service over a list of postings and the payments marked as posted. The mark and the postings are
  * made in one call, so a payment is never marked without its postings, or posted without its mark.
  */
final class LedgerAccounts(var postings: List[Posting], var marked: List[String]) extends Accounts:
  update def post(p: Payment): Unit =
    if !posted(p.id) then
      postings = postings ++ List(Posting(p.id, p.card, -p.amount), Posting(p.id, p.merchant, p.amount))
      marked = p.id :: marked

  def posted(id: String): Boolean = marked.contains(id)
  def postingsOf(id: String): List[Posting] = postings.filter(x => x.payment == id)
  def total: BigInt = postings.foldLeft(BigInt(0))((sum, x) => sum + x.amount)
