package frflow
package check

import frflow.fixtures.Concurrency

/** Flows at once in Lean: parTupled and parTraverse read as their branches in turn, with the proof asked that the
  * branches commute (`commute_i`, closed here by automation); atomically as its body; a race as the scheduler's choice,
  * the losing transaction all or nothing. End to end against Lean (see LeanLab).
  */
class LeanConcurrencySuite extends LeanLab:
  test("parTupled, parTraverse and a race with a transaction: proven of the models, the branches proven to commute") {
    val r = workflow(Concurrency.kb).check()
    for n <- List[Node[?]](Concurrency.restockContract, Concurrency.deliveriesContract, Concurrency.saleContract) do
      val c = of(r, n.id)
      assertEquals(c.status.toString, "proven", c.obligations.map(o => o.name.lean -> (o.status.toString, o.detail)))
      assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    for n <- List[Node[?]](Concurrency.restockContract, Concurrency.deliveriesContract) do
      assertEquals(result(of(r, n.id), "commute_0").map(_.status.toString), Some("proven"), of(r, n.id))
  }

  test("branches that do not commute (one reads what the other changes) are not proven to: commute_0 stays open") {
    import Concurrency.*
    val p = Param[BigInt => Flow[(BigInt, Unit)]]("peek", "the count read while goods come in")
    val c = Node.contract(p)("Peek", "Goods come in.", why = "A test.")((n, r, before, after) =>
      after(StockModel) === before(StockModel) + n)
      .examples()(expect(BigInt(2), World(StockModel -> BigInt(1), TillModel -> BigInt(0)), (BigInt(1), ()),
          World(StockModel -> BigInt(3), TillModel -> BigInt(0)), "two in"),
        expect(BigInt(0), World(StockModel -> BigInt(4), TillModel -> BigInt(0)), (BigInt(4), ()),
          World(StockModel -> BigInt(4), TillModel -> BigInt(0)), "none in"),
        never(BigInt(2), World(StockModel -> BigInt(1), TillModel -> BigInt(0)), (BigInt(1), ()),
          World(StockModel -> BigInt(1), TillModel -> BigInt(0)), "not lost"))
    val kb = KnowledgeBase("Peek", idea = "IDEA.md")(stockKept, tillKept, c)
      .implementProven(c)((n: Term[BigInt]) => (stock.count, stock.add(n)).parTupled)
    val r = workflow(kb).check()
    val got = of(r, "Peek")
    assertEquals(result(got, "impl").map(_.status.toString), Some("proven"), got)
    assertEquals(result(got, "commute_0").map(_.status.toString), Some("open"), got)
    assertEquals(got.status.toString, "open", got)
  }
