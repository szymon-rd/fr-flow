package frflow.fixtures

import frflow.*

/** A till that refunds: an `always` assumption of amounts says no amount is below nothing, and the refunding code
  * takes the till below it. The assumption stands in only for what comes from outside: a program that stores an
  * amount must keep it, and this one does not.
  */
object Refunds:
  import Service.{TillModel, till}

  val price = Param[BigInt => BigInt]("what an item costs")
  val refund = Param[BigInt => Flow[BigInt]]("refunding an item: what it gave back")

  def refunding(item: Term[BigInt]): Flow[BigInt] = till.ring(-price(item)).as(price(item))

  val refunded = Node.contract(refund)("Refunding an item gives back what it cost, more than nothing.")(
    (item, cost, before, after) => cost > BigInt(0) && after(TillModel) === before(TillModel) - cost)

  val costs = Node.contract("Every item costs something.")(forall((item: Term[BigInt]) => price(item) > BigInt(0)))
    .refines(refunded)
    .examples(allows(BigInt(3), BigInt(4), "three costs four"), forbids(BigInt(3), BigInt(0), "nothing is free"))

  val tillAdds = Node.assumption(till)(TillModel)("The till adds up what is rung.", why = "Memory.").refines(refunded)

  val noNegativeAmounts = Node.assumption("No amount is less than nothing.")(always[BigInt](x => x >= BigInt(0)))

  val kb: KnowledgeBase =
    KnowledgeBase("Refunds", idea = "IDEA.md")(refunded, costs, tillAdds, noNegativeAmounts)
      .implementProven(refunded)(refunding)
      .implementTested(costs)(item => item.abs + 1)
