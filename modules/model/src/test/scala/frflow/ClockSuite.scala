package frflow

import cats.effect.SyncIO
import frflow.fixtures.Timing
import frflow.flow.Flows

/** Time on flows: `now`, `sleep`, `waitUntil`, `timeout` and `every`, as Lean prints them, and run the same on the
  * clock's model, on a fake clock now and in `SyncIO`, for any start time and any delays a sleep adds.
  */
class ClockSuite extends munit.FunSuite:
  private val num = summon[LeanType[BigInt]]
  private def lean(f: AnyRef): String = Def(Lifted.flow(f, List(num), "f"), num, Some("f"), isFlow = true).lifted.lean
  private def steps(f: Flow[?]): Steps = Steps.of(f)._1

  /** Each interpretation, from a clock state: the result, and the clock's state after. */
  private val interpretations: List[(String, (Flow[?], ClockState) => (Any, ClockState))] = List(
    "on the model" -> { (f, c) => val (r, w) = Flows.onModels(steps(f), Map.empty, World(ClockModel -> c)); (r, w(ClockModel)) },
    "on a fake clock" -> { (f, c) => val k = FakeClock(c); (Flows.runNow(steps(f), Map.empty, Map(Clock.boundary -> k)), k.state) },
    "in SyncIO" -> { (f, c) =>
      val k = FakeClock(c); (Flows.run[SyncIO](steps(f), Map.empty, Map(Clock.boundary -> k), Nil).unsafeRunSync(), k.state) })

  test("now, sleep, waitUntil and timeout are steps on the clock, in Lean's do") {
    assertEquals(lean((t: Term[BigInt]) => Timing.waitThenRead(t)),
      """fun (t : Int) => do
        |    let t_1 ← Clock.now
        |    if (t_1 < t) then
        |      Clock.sleep (t - t_1)
        |      pure ()
        |    else
        |      pure ()
        |    Clock.now""".stripMargin)
    assertEquals(lean((d: Term[BigInt]) => Timing.napWithin(d)),
      """fun (d : Int) => do
        |    let start ← Clock.now
        |    let a ← Clock.sleep d
        |    let stop ← Clock.now
        |    pure (if ((stop - start) ≤ 5) then (some a) else none)""".stripMargin)
    assertEquals(lean((d: Term[BigInt]) => Flow.every(60)(Flow.sleep(d)).runs(Term.lit(List(BigInt(1), BigInt(2))))),
      """fun (d : Int) => do
        |    for tick in [1, 2] do
        |      Clock.sleep d
        |      Clock.sleep 60""".stripMargin)
  }

  test("the clock's flows run the same on the model, on a fake clock and in SyncIO, for any start and any delays") {
    val rnd = scala.util.Random(2)
    def n(x: BigInt) = Term.lit(x)
    for _ <- 1 to 200 do
      val c = ClockState(BigInt(rnd.between(-100, 100)), List.fill(rnd.between(0, 4))(BigInt(rnd.between(-5, 30))))
      val t = BigInt(rnd.between(-100, 200))
      val d = BigInt(rnd.between(-5, 10))
      for f <- List[Flow[?]](Timing.waitThenRead(n(t)), Timing.napWithin(n(d)), Timing.twoNights(n(t)),
          Flow.every(60)(Flow.sleep(n(d))).runs(Term.lit(List(1, 2, 3).map(BigInt(_))))) do
        val got = interpretations.map((how, run) => how -> run(f, c))
        got.foreach((how, r) => assertEquals(r, got.head._2, s"$how, from $c"))
  }

  test("a sleep wakes late by the next delay, never early; waitUntil reaches its time; timeout says whether it was late") {
    def onModel(f: Flow[?], c: ClockState) = interpretations.head._2(f, c)
    assertEquals(onModel(Flow.sleep(BigInt(5)), ClockState(BigInt(0), List[BigInt](3, 7))), ((), ClockState(BigInt(8), List[BigInt](7))))
    assertEquals(onModel(Flow.sleep(BigInt(-5)), ClockState(BigInt(0), List[BigInt](-3))), ((), ClockState(BigInt(0), Nil)))
    assertEquals(onModel(Timing.waitThenRead(BigInt(10)), ClockState(BigInt(4), Nil)), (BigInt(10), ClockState(BigInt(10), Nil)))
    assertEquals(onModel(Timing.napWithin(BigInt(3)), ClockState(BigInt(0), Nil)), (Some(()), ClockState(BigInt(3), Nil)))
    assertEquals(onModel(Timing.napWithin(BigInt(3)), ClockState(BigInt(0), List[BigInt](4))), (None, ClockState(BigInt(7), Nil)))
  }

  test("every: the scheduler runs the job, then sleeps the period on the clock; each run's start is handed on") {
    val clock = FakeClock(BigInt(1000))
    clock.delay(0, 5)
    var runs = List.empty[BigInt]
    val starts = List.newBuilder[BigInt]
    val job = Flow.every(60)(Flow.unit)
    job.schedule[SyncIO](clock, times = Some(3), started = starts += _)(() => SyncIO { runs = clock.time :: runs }).unsafeRunSync()
    assertEquals(starts.result(), List(BigInt(1000), BigInt(1060), BigInt(1125)))
    assertEquals(runs.reverse, List(BigInt(1000), BigInt(1060), BigInt(1125)))
    assertEquals(clock.time, BigInt(1185))
  }

  test("every, forever: each run built when the last ends, stack-safe (stopped here by the job after 5,000 runs)") {
    val clock = FakeClock(BigInt(0))
    var runs = 0
    val forever = Flow.every(60)(Flow.unit).schedule[SyncIO](clock)(() => SyncIO {
      runs += 1
      if runs == 5000 then throw IllegalStateException("enough")
    })
    assert(forever.attempt.unsafeRunSync().isLeft)
    assertEquals((runs, clock.time), (5000, BigInt(4999 * 60)))
  }
