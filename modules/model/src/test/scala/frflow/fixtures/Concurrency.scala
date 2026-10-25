package frflow.fixtures

import frflow.*

/** Flows at once: a shop's stock and its till, two boundaries; branches on disjoint parts commute, branches on the
  * same part commute when their changes do (two additions), and a sale is a transaction, raced against a timer.
  */
object Concurrency:
  trait Stock:
    def count: Flow[BigInt]
    def add(n: Term[BigInt]): Flow[Unit]
  trait Till:
    def total: Flow[BigInt]
    def ring(n: Term[BigInt]): Flow[Unit]

  object StockModel extends Stock, StateModel[BigInt]:
    def count = state.get
    def add(n: Term[BigInt]) = state.update(s => s + n)
  object TillModel extends Till, StateModel[BigInt]:
    def total = state.get
    def ring(n: Term[BigInt]) = state.update(s => s + n)

  /** The shop's own stock and till: what they hold, in memory. */
  final class MemoryStock(start: BigInt) extends Stock:
    private val held = java.util.concurrent.atomic.AtomicReference(start)
    def amount: BigInt = held.get
    def count = Flow.effect(held.get)
    def add(n: Term[BigInt]) = Flow.effect(n)(x => held.updateAndGet(_ + x))
  final class MemoryTill(start: BigInt) extends Till:
    private val held = java.util.concurrent.atomic.AtomicReference(start)
    def amount: BigInt = held.get
    def total = Flow.effect(held.get)
    def ring(n: Term[BigInt]) = Flow.effect(n)(x => held.updateAndGet(_ + x))

  val stock: Boundary[Stock] = Boundary[Stock]("stock", "the goods on the shelves")
  val till: Boundary[Till] = Boundary[Till]("till", "the money taken")

  val stockKept = Node.assumption(stock)(StockModel)("StockKept", "The stock counts what is added to it.", why = "Memory.")
    .implementedBy(a => MemoryStock(a), _.amount)
  val tillKept = Node.assumption(till)(TillModel)("TillKept", "The till adds up what is rung.", why = "Memory.")
    .implementedBy(a => MemoryTill(a), _.amount)
  val racesKept = Node.assumption(Races.boundary)(RacesModel)("RacesKept",
    "Which side of a race finishes first is the scheduler's: unknown, so a claim holds for either.", why = "Fibers.")
  val clockKept = Timing.clockKept

  /** Goods in, and their price rung, at once: different boundaries, so they commute. */
  def restock(n: Term[BigInt], price: Term[BigInt]): Flow[Unit] = (stock.add(n), till.ring(-price)).parTupled.void
  /** Two deliveries at once, to the same shelves: two additions, which commute. */
  def twoDeliveries(n: Term[BigInt], m: Term[BigInt]): Flow[List[Unit]] =
    Term.listOf[BigInt](List(n, m)).parTraverse(x => stock.add(x))
  /** A sale as one transaction: the count read and lowered in one step, never below zero. */
  def sell(n: Term[BigInt]): Flow[Unit] =
    Flow.atomically(stock.count.flatMap(s => Flow.whenA(s >= n)(stock.add(-n) *> till.ring(n))))
  /** A sale given five seconds: either it is done (or it had committed), or nothing changed. */
  def saleWithin(n: Term[BigInt]): Flow[Either[Unit, Unit]] = sell(n).race(Flow.sleep(BigInt(5)))

  private val restocking = Param[(BigInt, BigInt) => Flow[Unit]]("restocking", "goods in, their price paid")
  private val delivering = Param[(BigInt, BigInt) => Flow[List[Unit]]]("delivering", "two deliveries at once")
  private val selling = Param[BigInt => Flow[Either[Unit, Unit]]]("selling", "a sale given five seconds")

  private def at(s: BigInt, t: BigInt, races: List[Boolean] = Nil, now: BigInt = 0) =
    World(StockModel -> s, TillModel -> t, RacesModel -> races, ClockModel -> ClockState(now, Nil))

  val restockContract = Node.contract(restocking)("Restock",
    "Restocking adds the goods to the stock and takes their price from the till.", why = "Both, at once.")(
    (n, p, r, before, after) => after(StockModel) === before(StockModel) + n && after(TillModel) === before(TillModel) - p)
    .examples()(expect(BigInt(3), BigInt(10), at(1, 50), (), at(4, 40), "three in, ten paid"),
      expect(BigInt(0), BigInt(0), at(2, 5), (), at(2, 5), "nothing in"),
      reject(BigInt(3), BigInt(10), at(1, 50), (), at(4, 50), "never in without paying"))

  val deliveriesContract = Node.contract(delivering)("TwoDeliveries",
    "Two deliveries at once add both to the stock.", why = "Additions commute.")(
    (n, m, r, before, after) => after(StockModel) === before(StockModel) + n + m && after(TillModel) === before(TillModel))
    .examples()(expect(BigInt(3), BigInt(4), at(1, 0), List((), ()), at(8, 0), "three and four"),
      expect(BigInt(1), BigInt(1), at(0, 2), List((), ()), at(2, 2), "one each"),
      reject(BigInt(3), BigInt(4), at(1, 0), List((), ()), at(5, 0), "neither lost"))

  val saleContract = Node.contract(selling)("SaleWithin",
    "A sale given five seconds leaves the stock and the till as they were, or as the whole sale leaves them; never half.",
    why = "The sale is one transaction: cancelled by the timer, it left nothing, or had committed in full.")(
    (n, r, before, after) => (after(StockModel) === before(StockModel) && after(TillModel) === before(TillModel)) ||
      (after(StockModel) === before(StockModel) - n && after(TillModel) === before(TillModel) + n))
    .examples()(
      expect(BigInt(2), at(5, 0), Left(()), at(3, 2), "sold in time"),
      expect(BigInt(2), at(5, 0, List(false)), Right(()), at(5, 0, Nil, 5), "the timer first: nothing sold"),
      expect(BigInt(2), at(5, 0, List(false, true)), Right(()), at(3, 2, Nil, 5), "the timer first, but the sale had committed"),
      reject(BigInt(2), at(5, 0), Left(()), at(3, 0), "never half a sale"))

  val kb = KnowledgeBase("Concurrency", idea = "IDEA.md")(stockKept, tillKept, racesKept, clockKept, restockContract,
      deliveriesContract, saleContract)
    .implementProven(restockContract)((n: Term[BigInt], p: Term[BigInt]) => restock(n, p))
    .implementProven(deliveriesContract)((n: Term[BigInt], m: Term[BigInt]) => twoDeliveries(n, m))
    .implementProven(saleContract)((n: Term[BigInt]) => saleWithin(n))
