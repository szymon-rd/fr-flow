package frflow

import frflow.flow.Flows
import frflow.testing.ModelTests

class FlowSuite extends munit.FunSuite:
  private val flow = Def(Lifted.flow(restock, List(summon[LeanType[List[BigInt]]]), "restock"), summon[LeanType[BigInt]], Some("restock"), isFlow = true)
  private def steps = flow.lifted.built._2.termTree match { case Tree.Do(s) => s; case t => fail(s"not a flow: $t") }

  test("a flow prints as a do block over the boundary's class") {
    assertEquals(flow.lifted.lean,
      """fun (ds : (List Int)) => do
        |    let before ← Stock.count
        |    for d in ds do
        |      Stock.add d
        |    let after ← Stock.count
        |    pure (after - before)""".stripMargin)
    assertEquals(flow.lifted.boundaries, List(stock))
  }

  test("a value named in a for-comprehension is a let, computed once, named as the program names it") {
    val twice = Def(Lifted.flow(restockTwice, List(summon[LeanType[BigInt]]), "restockTwice"), summon[LeanType[BigInt]], Some("restockTwice"), isFlow = true)
    assertEquals(twice.lifted.lean,
      """fun (d : Int) => do
        |    let before ← Stock.count
        |    let twice := (d + d)
        |    Stock.add twice
        |    Stock.add twice
        |    let after ← Stock.count
        |    pure twice""".stripMargin)
    val s = twice.lifted.built._2.termTree match { case Tree.Do(s) => s; case t => fail(s"not a flow: $t") }
    val (r, w) = Flows.onModels(s, Map(twice.lifted.built._1.head -> BigInt(2)), World(StockModel -> BigInt(10)))
    assertEquals((r, w(StockModel)), (BigInt(4), BigInt(18)))
  }

  test("a flow runs on the models, and on an implementation, the same") {
    val (r, w) = Flows.onModels(steps, Map(flow.lifted.built._1.head -> List(BigInt(2), BigInt(3))), World(StockModel -> BigInt(10)))
    assertEquals((r, w(StockModel)), (BigInt(5), BigInt(15)))
    val counter = Counter(10)
    assertEquals(Flows.runNow(steps, Map(flow.lifted.built._1.head -> List(BigInt(2), BigInt(3))), Map(stock -> counter)), BigInt(5))
    assertEquals(counter.held, BigInt(15))
  }

  test("a boundary records calls; its model's operations are steps on its state") {
    assertEquals(stock.operations.map(_.getName), List("add", "count"))
    assertEquals(StockModel.field, "stock")
    assert(Steps.of(StockModel.add(Term.lit(BigInt(1))))._1.isInstanceOf[Steps.Modify])
    // a proven flow may not take a step of the outside world
    assert(Steps.effectful(Steps.of(Counter(0).count)._1))
  }

  private def stockKb(model: Node[?]) = KnowledgeBase("Shelf", idea = "IDEA.md")(model).testedWith(TestSettings(cases = 300, seed = 5))
  private def stockModel = Node.assumption(stock)(StockModel)("StockModel", "The stock counts the books added to it.", why = "A counter.")

  test("the project's own implementation of a boundary is tested against its model: generated runs, every operation reached") {
    val m = stockModel.implementedBy(c => Counter(c), _.held)
    val r = stockKb(m).test(m).get
    assertEquals(r.failure, None)
    assertEquals(r.coverage.map(c => c.part -> (c.held > 0)), List("add called" -> true, "count called" -> true))
    assertEquals(r.against, "the model StockModel")
    assert(r.notes.head.startsWith("Counter (the project's own code, tested): 300 runs"), r.notes)
  }

  test("an implementation that differs from its model is found on a generated run, shrunk to its smallest") {
    // Drops an addition of more than three books.
    final class Capped(var held: BigInt) extends Stock:
      def count = Flow.effect(held)
      def add(n: Term[BigInt]) = Flow.effect(n)(k => if k <= 3 then held += k)
    val m = stockModel.implementedBy(c => Capped(c), _.held)
    val f = stockKb(m).test(m).get.failure.getOrElse(fail("the difference was not found"))
    assertEquals(f.shown, "on Capped, from 0: add(4)")
    assertEquals(f.why, "after add(4), Capped holds 0, where the model holds 4")
  }

  test("an outside system is checked against the model on fewer runs, and said to be assumed") {
    val m = stockModel.checkedAgainst(c => Counter(c), _.held)
    val r = stockKb(m).testedWith(TestSettings(cases = 1000)).test(m).get
    assertEquals(r.failure, None)
    assert(r.notes.head.startsWith(s"Counter (an outside system: its model is assumed; these runs check it): ${ModelTests.OutsideRuns} runs"), r.notes)
  }
