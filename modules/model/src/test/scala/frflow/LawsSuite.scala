package frflow

import cats.effect.SyncIO
import frflow.fixtures.StockLaws
import frflow.flow.Flows

/** Cats' combinators on flows, as Lean prints them and as they run; and the relative monad's laws, at run time. */
class LawsSuite extends munit.FunSuite:
  private val num = summon[LeanType[BigInt]]
  private val nums = summon[LeanType[List[BigInt]]]
  private def lean(f: AnyRef, ins: LeanType[?]*): String =
    Def(Lifted.flow(f, ins.toList, "f"), num, Some("f"), isFlow = true).lifted.lean
  private def steps(f: Flow[?]): Steps = Steps.of(f)._1

  /** The three interpretations: on the model, on an implementation now, and on it in `SyncIO`. Each gives the result
    * and the stock after.
    */
  private val interpretations: List[(String, (Flow[?], BigInt) => (Any, BigInt))] = List(
    "on the model" -> { (f, held) => val (r, w) = Flows.onModels(steps(f), Map.empty, World(StockModel -> held)); (r, w(StockModel)) },
    "on an implementation" -> { (f, held) => val c = Counter(held); (Flows.runNow(steps(f), Map.empty, Map(stock -> c)), c.held) },
    "in SyncIO" -> { (f, held) =>
      val c = Counter(held); (Flows.run[SyncIO](steps(f), Map.empty, Map(stock -> c), Nil).unsafeRunSync(), c.held) })

  private def countsAfter(ds: Term[List[BigInt]]): Flow[List[BigInt]] = ds.traverse(d => stock.add(d) *> stock.count)
  private def peak(ds: Term[List[BigInt]]): Flow[BigInt] =
    ds.foldM(BigInt(0): Term[BigInt])((top, d) => stock.add(d) *> stock.count.map(n => (n > top).fold(n, top)))
  private def guarded(d: Term[BigInt]): Flow[BigInt] =
    Flow.whenA(d > 0)(stock.add(d)) *> Flow.unlessA(d > 0)(stock.add(BigInt(1))) *> stock.count
  private def restockLow(d: Term[BigInt]): Flow[BigInt] =
    Flow.ifM(stock.count.map(n => n < 10))(stock.add(d) *> stock.count, stock.count)
  private def both(d: Term[BigInt]): Flow[List[BigInt]] = Flow.sequence(List(stock.count, stock.add(d) *> stock.count))

  test("traverse is mapM, foldM is foldlM, and whenA, unlessA and ifM are Lean's if") {
    assertEquals(lean(countsAfter, nums),
      """fun (ds : (List Int)) => do
        |    ds.mapM fun d => do
        |      Stock.add d
        |      Stock.count""".stripMargin)
    assertEquals(lean(peak, nums),
      """fun (ds : (List Int)) => do
        |    ds.foldlM (init := 0) fun top d => do
        |      Stock.add d
        |      let n ← Stock.count
        |      pure (if (n > top) then n else top)""".stripMargin)
    assertEquals(lean(guarded, num),
      """fun (d : Int) => do
        |    if (d > 0) then
        |      Stock.add d
        |      pure ()
        |    else
        |      pure ()
        |    if (d > 0) then
        |      pure ()
        |    else
        |      Stock.add 1
        |      pure ()
        |    Stock.count""".stripMargin)
    assertEquals(lean(restockLow, num),
      """fun (d : Int) => do
        |    let holds ← do
        |      let n ← Stock.count
        |      pure (n < 10)
        |    if holds then
        |      Stock.add d
        |      Stock.count
        |    else
        |      Stock.count""".stripMargin)
  }

  test("the combinators run the same on the model, on an implementation and in SyncIO") {
    def at(f: Flow[?], held: BigInt) = interpretations.map((how, run) => how -> run(f, held))
    def same(f: Flow[?], held: BigInt, expected: (Any, BigInt)) = at(f, held).foreach((how, got) => assertEquals(got, expected, how))
    def ls(xs: Int*) = Term.lit(xs.toList.map(BigInt(_)))
    def n(x: Int) = Term.lit(BigInt(x))
    same(countsAfter(ls(2, 3)), 10, (List(BigInt(12), BigInt(15)), BigInt(15)))
    same(countsAfter(ls()), 10, (Nil, BigInt(10)))
    same(peak(ls(4, -6, 1)), 0, (BigInt(4), BigInt(-1)))
    same(guarded(n(5)), 1, (BigInt(6), BigInt(6)))
    same(guarded(n(-5)), 1, (BigInt(2), BigInt(2)))
    same(restockLow(n(5)), 3, (BigInt(8), BigInt(8)))
    same(restockLow(n(5)), 30, (BigInt(30), BigInt(30)))
    same(both(n(2)), 1, (List(BigInt(1), BigInt(3)), BigInt(3)))
  }

  test("the laws' two sides are different programs") {
    for (law, eq) <- List[(String, Term[BigInt] => RelativeMonad.IsEq[Flow[BigInt]])](
        "left unit" -> StockLaws.leftUnit, "right unit" -> StockLaws.rightUnit, "associativity" -> StockLaws.associativity) do
      assertNotEquals(lean((a: Term[BigInt]) => eq(a).lhs, num), lean((a: Term[BigInt]) => eq(a).rhs, num), law)
  }

  test("the relative monad's laws hold on the model, on an implementation and in SyncIO, on generated inputs") {
    val rnd = scala.util.Random(38)
    val inputs = List.fill(200)((BigInt(rnd.between(-20, 21)), BigInt(rnd.between(-20, 21))))
    for
      (a, held) <- inputs
      (law, eq) <- List("left unit" -> StockLaws.leftUnit(Term.lit(a)), "right unit" -> StockLaws.rightUnit(Term.lit(a)),
        "associativity" -> StockLaws.associativity(Term.lit(a)))
      (how, run) <- interpretations
    do assertEquals(run(eq.lhs, held), run(eq.rhs, held), s"$law $how, $a delivered to $held")
  }
