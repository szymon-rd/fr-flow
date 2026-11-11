package payments

import frflow.*

/** The stream at work. A card may spend 100 a day; two payments of 80 on one card and one day arrive. */
class PaymentsExamples extends FrFlowExamples(payments):
  private val start = Pipeline(Spending(100, Nil), Books(Nil, Nil), 0)
  private val coffee = Payment(0, "p1", "card-1", "cafe", 80, 1)
  private val drinks = Payment(1, "p2", "card-1", "bar", 80, 1)
  private val charged = List(Posting("p1", "card-1", -80), Posting("p1", "cafe", 80))
  private val approved = Spending(100, List(Decision("p1", "card-1", 1, 80, true)))

  /** What a crash between the decision and the posting leaves: decided, nothing posted, the position not moved. */
  private val crashed = Pipeline(approved, Books(Nil, Nil), 0)

  /** What another instance handling the same payment leaves, between this call's decision and its posting. */
  private val handled = Pipeline(approved, Books(charged, List("p1")), 1)

  example("a payment within the limit: approved, posted, the position past it"):
    val done = Processor.handle(start, coffee)
    done._1 && (Books.made(done._2.books.postings, "p1") is charged) && (done._2.committed is BigInt(1))

  example("the next payment takes the card over its limit of the day: declined, nothing posted"):
    val done = Processor.handle(Processor.handle(start, coffee)._2, drinks)
    !done._1 && Books.made(done._2.books.postings, "p2").isEmpty && (done._2.committed is BigInt(2))

  example("the same payment delivered again: the answer it got, nothing changed"):
    Processor.handle(Processor.handle(start, coffee)._2, coffee) === Processor.handle(start, coffee)

  example("after a crash between the decision and the posting, delivered again: posted once"):
    val done = Processor.handle(crashed, coffee)
    done._1 && (Books.made(done._2.books.postings, "p1") is charged) && (done._2.committed is BigInt(1))

  example("another instance handles the payment between this call's decision and its posting: posted once"):
    Processor.handleAmongOthers(start, Map(BigInt(2) -> handled), coffee)._2.forall(step =>
      Books.made(step._2.books.postings, "p1").isEmpty || (Books.made(step._2.books.postings, "p1") is charged))

  // The three first versions.

  example("eager, stopped after its first step: the position is past a payment that is not applied"):
    !Eager.eagerAmongOthers(start, Map.empty[BigInt, Pipeline], coffee)._2.forall(step =>
      (step._2.committed is BigInt(0)) || Pipeline.applied(step._2, "p1"))

  example("blind, the payment delivered again: its card is charged twice"):
    Books.made(Blind.blindHandle(Blind.blindHandle(start, coffee)._2, coffee)._2.books.postings, "p1") is
      (charged ++ charged)

  example("hasty, another payment approved between its check and its record: the card is over its limit"):
    val other = Spending(100, List(Decision("p2", "card-1", 1, 80, true)))
    !Hasty.hastyAmongOthers(Spending(100, Nil), Map(BigInt(2) -> other), coffee)._2.forall(step =>
      Spending.withinLimits(step._2))

  example("the limits service, that payment decided first: declined"):
    val other = Spending(100, List(Decision("p2", "card-1", 1, 80, true)))
    !Limits.authorise(other, coffee)._1
