package payments

import frflow.*
import CardLimits.limits
import ConsumerOffsets.offsets
import EagerHandler.eager
import HastyHandler.hasty
import Ledger.ledger
import PaymentHandler.{applied, handler}

/** The stream at work. A card may spend 100 a day; two payments of 80 on one card and one day arrive. A state
  * is given as an object of the class that implements the trait (`holding`), and what the ledger, the card limits
  * and the offsets say is asked of them as the handler has them.
  */
class PaymentsExamples extends FrFlowExamples(payments):
  private val (p1, p2, card) = (PaymentId("p1"), PaymentId("p2"), CardId("card-1"))
  private val coffee = Payment(0, p1, card, MerchantId("cafe"), 80, 1)
  private val drinks = Payment(1, p2, card, MerchantId("bar"), 80, 1)
  private val charged =
    List(Posting(p1, Account.OfCard(card), -80), Posting(p1, Account.OfMerchant(MerchantId("cafe")), 80))
  private val coffeeApproved = Decision(p1, card, 1, 80, true)
  private val drinksApproved = Decision(p2, card, 1, 80, true)

  /** The handler before any payment. */
  private val start = handler.holding(
    StreamPaymentHandler(RecordedLimits(BigInt(100), Nil), PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))

  /** What a crash between the decision and the posting leaves: decided, nothing posted, the offset not committed. */
  private val crashed = handler.holding(StreamPaymentHandler(RecordedLimits(BigInt(100), List(coffeeApproved)),
    PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))

  /** What another instance handling the same payment leaves, between this call's decision and its posting. */
  private val handled = handler.holding(StreamPaymentHandler(RecordedLimits(BigInt(100), List(coffeeApproved)),
    PostingLedger(charged, List(p1)), CommittedOffset(BigInt(1))))

  example("a payment within the limit: approved, posted, its offset committed"):
    val done = handler.handle(coffee).in(start)
    done.result && (ledger.postingsOf(p1).in(done.after) is charged) &&
      (offsets.committed.in(done.after) is BigInt(1))

  example("the next payment takes the card over its limit of the day: declined, nothing posted"):
    val done = handler.handle(drinks).in(handler.handle(coffee).in(start).after)
    !done.result && ledger.postingsOf(p2).in(done.after).isEmpty &&
      (offsets.committed.in(done.after) is BigInt(2))

  example("the same payment delivered again: the answer it got, nothing changed"):
    val first = handler.handle(coffee).in(start)
    handler.handle(coffee).in(first.after).result && (handler.handle(coffee).in(first.after).after === first.after)

  example("after a crash between the decision and the posting, delivered again: posted once"):
    val done = handler.handle(coffee).in(crashed)
    done.result && (ledger.postingsOf(p1).in(done.after) is charged) &&
      (offsets.committed.in(done.after) is BigInt(1))

  example("another instance handles the payment between this call's decision and its posting: posted once"):
    handler.handle(coffee).in(start).among(handler.nobody.updated(BigInt(2), handled)).steps.forall(step =>
      ledger.postingsOf(p1).in(step._2).isEmpty || (ledger.postingsOf(p1).in(step._2) is charged))

  // The two first versions.

  example("eager, stopped after its first step: the committed offset is past a payment that is not applied"):
    val start = eager.holding(
      CommitFirstHandler(RecordedLimits(BigInt(100), Nil), PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))
    !eager.handle(coffee).in(start).steps.forall(step =>
      (offsets.committed.in(step._2) is BigInt(0)) || applied(p1, step._2))

  example("hasty, another payment approved between its check and its record: it approves and posts a payment " +
      "the card limits declined"):
    val start = hasty.holding(
      CheckThenActHandler(RecordedLimits(BigInt(100), Nil), PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))
    val filled = hasty.holding(CheckThenActHandler(RecordedLimits(BigInt(100), List(drinksApproved)),
      PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))
    val run = hasty.handle(coffee).in(start).among(hasty.nobody.updated(BigInt(3), filled))
    run.result && !limits.approved(p1).in(run.after) && ledger.posted(p1).in(run.after)

  example("the handler, on a card another instance has just filled: declined, nothing posted"):
    val filled = handler.holding(StreamPaymentHandler(RecordedLimits(BigInt(100), List(drinksApproved)),
      PostingLedger(Nil, Nil), CommittedOffset(BigInt(0))))
    val done = handler.handle(coffee).in(filled)
    !done.result && ledger.postingsOf(p1).in(done.after).isEmpty
