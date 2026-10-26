package frflow

import cats.effect.{IO, SyncIO}
import cats.effect.unsafe.implicits.global
import frflow.fixtures.Concurrency
import frflow.fixtures.Concurrency.*
import frflow.flow.Flows

/** Flows at once: parTupled, parTraverse, race and atomically, as Lean prints them (the branches in turn, and what the
  * proof must show: that they commute), as they run on the models (in turn) and at run time (on fibers in IO, in turn in
  * SyncIO), the generated interleaved runs, and Parallel's law: of branches that commute, parTupled is tupled.
  */
class ConcurrencySuite extends munit.FunSuite:
  private val num = summon[LeanType[BigInt]]
  private def lifted(f: AnyRef, ins: Int = 2) = Def(Lifted.flow(f, List.fill(ins)(num), "f"), num, Some("f"), isFlow = true).lifted
  private def steps(f: Flow[?]): Steps = Steps.of(f)._1
  private def n(x: Int): Term[BigInt] = Term.lit(BigInt(x))

  test("parTupled reads as tupled, and the proof is asked that its branches commute") {
    val l = lifted((a: Term[BigInt], b: Term[BigInt]) => restock(a, b))
    assertEquals(l.lean,
      """fun (a : Int) (b : Int) => do
        |    let _ ← do
        |      let left ← Stock.add a
        |      let right ← Till.ring (-b)
        |      pure (left, right)
        |    pure ()""".stripMargin)
    val List(c) = l.commutes
    assertEquals(c.free, List("a" -> "Int", "b" -> "Int"))
    assertEquals(c.first, List("let left ← do", "  Stock.add a", "let right ← do", "  Till.ring (-b)", "pure (left, right)"))
    assertEquals(c.second, List("let right ← do", "  Till.ring (-b)", "let left ← do", "  Stock.add a", "pure (left, right)"))
  }

  test("parTraverse reads as traverse; the proof is asked that any two of its elements commute") {
    val l = lifted((a: Term[BigInt], b: Term[BigInt]) => twoDeliveries(a, b))
    assert(l.lean.contains("[a, b].mapM fun x => do"), l.lean)
    val List(c) = l.commutes
    assertEquals(c.hyps, List("x_one ∈ [a, b]", "x_two ∈ [a, b]", "x_one ≠ x_two"))
    assertEquals(c.first, List("let one ← do", "  Stock.add x_one", "let two ← do", "  Stock.add x_two", "pure (one, two)"))
  }

  test("atomically reads as its body; a race as the scheduler's choice, the losing transaction all or nothing") {
    val l = lifted((a: Term[BigInt]) => saleWithin(a), 1)
    assert(l.lean.contains("let leftFirst ← Races.leftFirst"), l.lean)
    assert(l.lean.contains("let committed ← Races.committed"), l.lean)
    assertEquals(l.boundaries.map(_.name).toSet, Set("races", "stock", "till", "clock"))
  }

  test("what proven code may not hold: a transaction inside one, a branch that may fail, a race of two transactions") {
    intercept[IllegalArgumentException](steps(Flow.atomically(sell(n(1)))))
    val failing = Boundary.failing[Stock]("flaky", "a stock that may be down")(Term.lit(BigInt(0)))
    val e = intercept[IllegalArgumentException](lifted((a: Term[BigInt], b: Term[BigInt]) => (failing.ops.add(a), stock.add(b)).parTupled).lean)
    assert(e.getMessage.contains("may fail"), e.getMessage)
    val r = intercept[IllegalArgumentException](lifted((a: Term[BigInt]) => sell(a).race(sell(a)), 1).lean)
    assert(r.getMessage.contains("a race in proven code"), r.getMessage)
  }

  test("the examples hold of the contracts and of the flows, run in turn on the models and interleaved on fibers") {
    assertEquals(Concurrency.kb.problems.filterNot(_.toString.contains("a root is required")), Nil)
    for c <- List[Node[?]](restockContract, deliveriesContract, saleContract) do
      val rs = Concurrency.kb.exampleResults(c)
      assert(rs.forall(r => r.contract == "ok" && r.implementation.forall(_ == "ok")), rs)
      assert(rs.exists(_.example.note.contains("runs on fibers, interleaved")), rs.map(_.example.note))
  }

  test("the interleaved runs catch branches that share state outside a transaction, where the commutation proof does not") {
    // Each delivery reads the count and puts it back raised: whole branches commute (either order adds both), but two at
    // once can both read the old count, and one addition is lost.
    trait Shelf:
      def count: Flow[BigInt]
      def put(n: Term[BigInt]): Flow[Unit]
    object ShelfModel extends Shelf, StateModel[BigInt]:
      def count = state.get
      def put(n: Term[BigInt]) = state.set(n)
    final class MemoryShelf(start: BigInt) extends Shelf:
      private val held = java.util.concurrent.atomic.AtomicReference(start)
      def amount: BigInt = held.get
      def count = Flow.effect(held.get)
      def put(n: Term[BigInt]) = Flow.effect(n)(x => held.set(x))
    val shelf = Boundary[Shelf]("shelf", "goods on a shelf")
    val kept = Node.assumption(shelf)(ShelfModel)("The shelf holds what is put.", why = "Memory.")
      .implementedBy(a => MemoryShelf(a), _.amount)
    val p = Param[(BigInt, BigInt) => Flow[List[Unit]]]("two deliveries, each read and put back")
    def add(x: Term[BigInt]) = shelf.ops.count.flatMap(s => shelf.ops.put(s + x))
    val c = Node.contract(p)("Both deliveries are on the shelf.", why = "A test.")(
      (a, b, r, before, after) => after(ShelfModel) === before(ShelfModel) + a + b)
      .examples()(allows(BigInt(3), BigInt(4), World(ShelfModel -> BigInt(1)), List((), ()), World(ShelfModel -> BigInt(8)), "both"),
        forbids(BigInt(3), BigInt(4), World(ShelfModel -> BigInt(1)), List((), ()), World(ShelfModel -> BigInt(5)), "not one lost"))
    def kb(f: Term[BigInt] => Flow[Unit]) = KnowledgeBase("ByHand", idea = "IDEA.md")(kept, c)
      .implementProven(c)((a: Term[BigInt], b: Term[BigInt]) => Term.listOf[BigInt](List(a, b)).parTraverse(f))
    val lost = kb(add).exampleResults(c).filter(_.example.note.contains("on fibers"))
    assert(lost.exists(_.implementation.exists(_.contains("its branches interleaved"))), lost)
    val kept2 = kb(x => Flow.atomically(add(x))).exampleResults(c).filter(_.example.note.contains("on fibers"))
    assert(kept2.forall(_.implementation.contains("ok")), kept2)
  }

  private def timed[A](io: IO[A]): (A, Long) =
    val t0 = System.nanoTime
    val a = io.unsafeRunSync()
    (a, (System.nanoTime - t0) / 1000000)

  test("in IO the branches run at once, on fibers; in SyncIO, in turn") {
    val clock = Map[Boundary[?], Any](Clock.boundary -> SystemClock)
    val both = steps((Flow.sleep(n(1)), Flow.sleep(n(1))).parTupled)
    val (r, ms) = timed(Flows.run[IO](both, Map.empty, clock, Nil))
    assertEquals(r, ((), ()))
    assert(ms < 1800, s"$ms ms: the two sleeps ran in turn")
    val order = java.util.concurrent.ConcurrentLinkedQueue[String]()
    val noted = steps((Flow.effect(order.add("left")), Flow.effect(order.add("right"))).parTupled)
    Flows.run[SyncIO](noted, Map.empty, Map.empty, Nil).unsafeRunSync()
    assertEquals(order.toArray.toList, List("left", "right"))
    val many = steps(Term.listOf[BigInt]((1 to 8).toList.map(n)).parTraverseN(4)(_ => Flow.sleep(n(1))))
    val (_, ms8) = timed(Flows.run[IO](many, Map.empty, clock, Nil))
    assert(ms8 >= 1900 && ms8 < 3500, s"$ms8 ms: eight sleeps of a second, four at once, take two")
  }

  test("a race cancels its loser, which runs its finalizer; a transaction once begun is not cancelled") {
    val finalized = java.util.concurrent.atomic.AtomicBoolean(false)
    val clock = Map[Boundary[?], Any](Clock.boundary -> SystemClock)
    val loser = Flow.sleep(n(5)).guarantee[BigInt](Flow.effect(finalized.set(true)))
    val (r, ms) = timed(Flows.run[IO](steps(loser.race(Flow.unit)), Map.empty, clock, Nil))
    assertEquals(r, Right(()))
    assert(ms < 2000 && finalized.get, s"$ms ms, finalized: ${finalized.get}")
    // A sale raced against an instant timer: the stock and the till agree, whoever won.
    for _ <- 1 to 20 do
      val (s, t) = (MemoryStock(5), MemoryTill(0))
      val impls = Map[Boundary[?], Any](stock -> s, till -> t, Clock.boundary -> FakeClock(0))
      Flows.run[IO](steps(saleWithin(n(2))), Map.empty, impls, Nil, Some(IO.cede)).unsafeRunSync()
      assert((s.amount, t.amount) == (BigInt(5), BigInt(0)) || (s.amount, t.amount) == (BigInt(3), BigInt(2)), (s.amount, t.amount))
  }

  test("transactions at once give what they give one after the other: 200 sales of one item from 100") {
    val (s, t) = (MemoryStock(100), MemoryTill(0))
    val impls = Map[Boundary[?], Any](stock -> s, till -> t)
    val rnd = java.util.SplittableRandom(5)
    val pause = IO(rnd.synchronized(rnd.nextInt(200))).flatMap(us => IO.sleep(scala.concurrent.duration.Duration(us.toLong, java.util.concurrent.TimeUnit.MICROSECONDS)))
    val sales = steps(Term.listOf[BigInt](List.fill(200)(n(1))).parTraverseN(16)(x => sell(x)))
    Flows.run[IO](sales, Map.empty, impls, Nil, Some(pause)).unsafeRunSync()
    assertEquals((s.amount, t.amount), (BigInt(0), BigInt(100)))
  }

  test("Parallel's law: of branches that commute, parTupled gives what tupled gives, on the models and in IO") {
    val rnd = scala.util.Random(11)
    for _ <- 1 to 50 do
      val (a, b, s0, t0) = (BigInt(rnd.between(-5, 6)), BigInt(rnd.between(-5, 6)), BigInt(rnd.between(0, 9)), BigInt(rnd.between(0, 9)))
      val (fa, fb) = (stock.add(Term.lit(a)) *> stock.count, till.ring(Term.lit(b)) *> till.total)
      val w = World(StockModel -> s0, TillModel -> t0)
      assertEquals(Flows.onModels(steps((fa, fb).parTupled), Map.empty, w), Flows.onModels(steps((fa, fb).tupled), Map.empty, w))
      def io(f: Flow[?]) =
        val (s, t) = (MemoryStock(s0), MemoryTill(t0))
        (Flows.run[IO](steps(f), Map.empty, Map(stock -> s, till -> t), Nil, Some(IO.cede)).unsafeRunSync(), s.amount, t.amount)
      assertEquals(io((fa, fb).parTupled), io((fa, fb).tupled))
  }
