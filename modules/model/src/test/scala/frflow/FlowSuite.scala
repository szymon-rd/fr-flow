package frflow

/** A shelf's stock as a boundary: a flow over it is printed as a Lean `do` block, run on its model, and run on an
  * implementation, which is checked against the model.
  */
trait Stock:
  def count: Flow[BigInt]
  def add(n: Term[BigInt]): Flow[Unit]

object StockModel extends Stock, StateModel[BigInt]:
  def count = state.get
  def add(n: Term[BigInt]) = state.update(c => c + n)

/** The stock in production: a mutable counter. */
final class Counter(var held: BigInt) extends Stock:
  def count = Flow.effect(held)
  def add(n: Term[BigInt]) = Flow.effect(n)(k => held += k)

val stock = Boundary[Stock]("stock", "the books in stock")

/** Restocks each of the deliveries, then says how many there are. */
def restock(ds: Term[List[BigInt]]): Flow[BigInt] =
  for
    before <- stock.count
    _ <- ds.traverse_(d => stock.add(d))
    after <- stock.count
  yield after - before

class FlowSuite extends munit.FunSuite:
  private val flow = Def(Lifted.flow(restock, summon[LeanType[List[BigInt]]], "restock"), summon[LeanType[BigInt]], Some("restock"), isFlow = true)
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
