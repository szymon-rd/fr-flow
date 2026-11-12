package payments

import frflow.*
import Eager.eager
import Hasty.hasty
import Processor.processor

/** The stream at work. A card may spend 100 a day; two payments of 80 on one card and one day arrive. Each
  * service is given as an object of the class that implements it (`holding`).
  */
class PaymentsExamples extends FrFlowExamples(payments):
  private val (p1, p2, card) = (PaymentId("p1"), PaymentId("p2"), CardId("card-1"))
  private val coffee = Payment(0, p1, card, MerchantId("cafe"), 80, 1)
  private val drinks = Payment(1, p2, card, MerchantId("bar"), 80, 1)
  private val charged =
    List(Posting(p1, Account.OfCard(card), -80), Posting(p1, Account.OfMerchant(MerchantId("cafe")), 80))
  private val coffeeApproved = Decision(p1, card, 1, 80, true)
  private val drinksApproved = Decision(p2, card, 1, 80, true)

  /** The processor before any payment. */
  private val start = processor.holding(
    StreamProcessor(SpendLimits(BigInt(100), Nil), LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))

  /** What a crash between the decision and the posting leaves: decided, nothing posted, the position not moved. */
  private val crashed = processor.holding(StreamProcessor(SpendLimits(BigInt(100), List(coffeeApproved)),
    LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))

  /** What another instance handling the same payment leaves, between this call's decision and its posting. */
  private val handled = processor.holding(StreamProcessor(SpendLimits(BigInt(100), List(coffeeApproved)),
    LedgerAccounts(charged, List(p1)), OffsetCheckpoint(BigInt(1))))

  example("a payment within the limit: approved, posted, the position past it"):
    val done = processor.handle(coffee).in(start)
    done.result && (processor.postingsOf(p1).in(done.after) is charged) &&
      (processor.position.in(done.after) is BigInt(1))

  example("the next payment takes the card over its limit of the day: declined, nothing posted"):
    val done = processor.handle(drinks).in(processor.handle(coffee).in(start).after)
    !done.result && processor.postingsOf(p2).in(done.after).isEmpty &&
      (processor.position.in(done.after) is BigInt(2))

  example("the same payment delivered again: the answer it got, nothing changed"):
    val first = processor.handle(coffee).in(start)
    processor.handle(coffee).in(first.after).result && (processor.handle(coffee).in(first.after).after === first.after)

  example("after a crash between the decision and the posting, delivered again: posted once"):
    val done = processor.handle(coffee).in(crashed)
    done.result && (processor.postingsOf(p1).in(done.after) is charged) &&
      (processor.position.in(done.after) is BigInt(1))

  example("another instance handles the payment between this call's decision and its posting: posted once"):
    processor.handle(coffee).in(start).among(processor.nobody.updated(BigInt(2), handled)).steps.forall(step =>
      processor.postingsOf(p1).in(step._2).isEmpty || (processor.postingsOf(p1).in(step._2) is charged))

  // The two first versions.

  example("eager, stopped after its first step: the position is past a payment that is not applied"):
    val start = eager.holding(
      EagerProcessor(SpendLimits(BigInt(100), Nil), LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))
    !eager.handle(coffee).in(start).steps.forall(step =>
      (eager.position.in(step._2) is BigInt(0)) || eager.applied(p1).in(step._2))

  example("hasty, another payment approved between its check and its record: it approves and posts a payment " +
      "the limits service declined"):
    val start = hasty.holding(
      HastyProcessor(SpendLimits(BigInt(100), Nil), LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))
    val filled = hasty.holding(HastyProcessor(SpendLimits(BigInt(100), List(drinksApproved)),
      LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))
    val run = hasty.handle(coffee).in(start).among(hasty.nobody.updated(BigInt(3), filled))
    run.result && !hasty.approved(p1).in(run.after) && hasty.posted(p1).in(run.after)

  example("the processor, on a card another instance has just filled: declined, nothing posted"):
    val filled = processor.holding(StreamProcessor(SpendLimits(BigInt(100), List(drinksApproved)),
      LedgerAccounts(Nil, Nil), OffsetCheckpoint(BigInt(0))))
    val done = processor.handle(coffee).in(filled)
    !done.result && processor.postingsOf(p1).in(done.after).isEmpty
