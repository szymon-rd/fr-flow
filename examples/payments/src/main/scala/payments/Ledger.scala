package payments

import language.experimental.captureChecking
import language.experimental.separationChecking
import caps.Mutable
import frflow.*

/** The ledger: each payment is posted to the books once, as two sides that cancel. */
trait Ledger extends Mutable:
  /** Posts a payment's two sides, unless it is posted already. */
  update def post(payment: Payment): Unit
  /** Whether a payment is marked as posted. */
  def posted(id: PaymentId): Boolean
  /** The postings made for a payment, in the order made: none, or its two sides. */
  def postingsOf(id: PaymentId): List[Posting]
  /** All the money in the books: the sum of every posting. */
  def total: BigInt

object Ledger:
  val ledger = Declaration[Ledger]("the ledger: each payment posted to the books once")

  val postedIsMarked = Node.claim("A payment posted is marked as posted.")(
    forall((p: Term[Payment]) => ledger.posted(p.id).in(ledger.post(p).after)))

  val postIsRepeatable = Node.claim("Posting a payment again changes nothing.")(
    forall((p: Term[Payment]) => ledger.post(p).in(ledger.post(p).after).after === ledger.post(p).after))

  val postKeepsTotal = Node.claim("Posting a payment leaves the total of the books as it was.")(
    forall((p: Term[Payment]) => ledger.total.in(ledger.post(p).after) === ledger.total))

  val postKeepsPosted = Node.claim("Posting a payment leaves every payment posted before marked as posted.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      ledger.posted(id) implies ledger.posted(id).in(ledger.post(p).after)))

  val postKeepsMarks = Node.claim("Posting a payment leaves a payment that has postings only if it is marked " +
      "so.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      (ledger.postingsOf(id).isEmpty || ledger.posted(id)) implies
        (ledger.postingsOf(id).in(ledger.post(p).after).isEmpty || ledger.posted(id).in(ledger.post(p).after))))

  val postAddsToNoPayment = Node.claim("Posting a payment adds nothing to the postings of a payment that has " +
      "some, where a payment with postings is marked.")(
    forall((id: Term[PaymentId], p: Term[Payment]) =>
      (ledger.postingsOf(id).isEmpty || ledger.posted(id)) implies
        (ledger.postingsOf(id).isEmpty ||
          ledger.postingsOf(id).in(ledger.post(p).after) === ledger.postingsOf(id))))

/** The ledger kept as its postings and the payments marked as posted. The mark and the postings are
  * made in one call, so a payment is never marked without its postings, or posted without its mark.
  */
final class PostingLedger(var postings: List[Posting], var marked: List[PaymentId]) extends Ledger:
  update def post(payment: Payment): Unit =
    if !posted(payment.id) then
      postings = postings ++ List(Posting(payment.id, Account.OfCard(payment.card), -payment.amount),
        Posting(payment.id, Account.OfMerchant(payment.merchant), payment.amount))
      marked = payment.id :: marked

  def posted(id: PaymentId): Boolean = marked.contains(id)
  def postingsOf(id: PaymentId): List[Posting] = postings.filter(x => x.payment == id)
  def total: BigInt = postings.foldLeft(BigInt(0))((sum, x) => sum + x.amount)
