package frflow.fixtures

import frflow.*

/** A service whose root is stated of its flow: selling an item rings its price on the till. The root's parts are what
  * the flow calls: the price's contract, and the till's model.
  */
object Service:
  trait Till:
    def ring(n: Term[BigInt]): Flow[Unit]

  object TillModel extends Till, StateModel[BigInt]:
    def ring(n: Term[BigInt]) = state.update(t => t + n)

  val till: Boundary[Till] = Boundary[Till]("till", "the money taken")

  val price = Param[BigInt => BigInt]("what an item costs")
  val sell = Param[BigInt => Flow[BigInt]]("selling an item: what it cost")

  def selling(item: Term[BigInt]): Flow[BigInt] = till.ring(price(item)).as(price(item))

  val sold = Node.contract(sell)("Selling an item takes money: the till gains what it cost, more than nothing.")(
    (item, cost, before, after) => cost > BigInt(0) && after(TillModel) === before(TillModel) + cost)

  val pricePositive = Node.contract("Every item costs something.")(forall((item: Term[BigInt]) => price(item) > BigInt(0)))
    .refines(sold)
    .examples(allows(BigInt(3), BigInt(4), "three costs four"), allows(BigInt(-5), BigInt(6), "minus five costs six"),
      forbids(BigInt(3), BigInt(0), "nothing is free"))

  /** Weaker than the root needs: an item may be free. */
  val priceNotNegative = Node.contract("No item costs less than nothing.")(forall((item: Term[BigInt]) => price(item) >= BigInt(0)))
    .refines(sold)
    .examples(allows(BigInt(3), BigInt(4), "three costs four"), allows(BigInt(2), BigInt(0), "two is free"),
      forbids(BigInt(3), BigInt(-1), "never paid to take"))

  val tillKept = Node.assumption(till)(TillModel)("The till adds up what is rung.", why = "Memory.").refines(sold)

  def kb(part: Node[BigInt => BigInt] = pricePositive): KnowledgeBase =
    KnowledgeBase("Service", idea = "IDEA.md")(sold, part, tillKept)
      .implementProven(sold)(selling)
      .implementTested(part)(item => item.abs + 1)
