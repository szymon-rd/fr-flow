package frflow

/** What the clock's model holds: the time now, in seconds, and the delays still to come. A sleep of `d` seconds wakes
  * `d` seconds later plus the next delay (a delay below zero counts as zero), which the proofs do not know: a flow is
  * proven for every start time and every list of delays, so for every wake-up that is not early.
  */
final case class ClockState(now: BigInt, delays: List[BigInt])
object ClockState extends Data[ClockState]

/** Time, as a boundary: the time now, in seconds, and sleeping. Steps take no time (the synchronous hypothesis):
  * time passes at a sleep, and between the system's events. `Flow.now`, `Flow.sleep(d)`, `Flow.waitUntil(t)`,
  * `f.timeout(d)` and `Flow.every(period)(job)` are written on it.
  */
trait Clock:
  /** The time now, in seconds. */
  def now: Flow[BigInt]
  /** Waits `seconds` (none when below zero); it may wake later, never earlier. */
  def sleep(seconds: Term[BigInt]): Flow[Unit]

object Clock:
  val boundary: Boundary[Clock] = Boundary[Clock]("clock", "the time now, in seconds, and sleeping")

/** The clock as the proofs see it: the time in the state, a sleep moving it on by the time asked and the next delay.
  * Nothing else moves it: a flow that reads the clock twice, with no sleep between, reads the same time. That the clock
  * never goes backwards is what the developer assumes of it (`Node.assumption(Clock.boundary)(ClockModel)(…)`).
  */
object ClockModel extends Clock, StateModel[ClockState]:
  def now: Flow[BigInt] = state.get.map(c => c.now)
  def sleep(seconds: Term[BigInt]): Flow[Unit] =
    state.update(c => ClockState(c.now + seconds.max(0) + c.delays.headOption.getOrElse(0).max(0), c.delays.drop(1)))

/** The computer's clock: seconds since 1970, and the thread put to sleep. Outside the proofs: assumed, not tested. */
object SystemClock extends Clock:
  def now: Flow[BigInt] = Flow.effect(BigInt(System.currentTimeMillis / 1000))
  def sleep(seconds: Term[BigInt]): Flow[Unit] = Flow.effect(seconds)(s => if s > 0 then Thread.sleep((s * 1000).toLong))

/** A clock for tests, which does what the model does: a sleep returns at once, the time moved on. `advance` moves it
  * as time passing between events would; the delays let a test wake its sleepers late, as a loaded machine would.
  */
final class FakeClock(start: ClockState) extends Clock:
  private var held = start
  def this(now: BigInt) = this(ClockState(now, Nil))
  def state: ClockState = synchronized(held)
  def time: BigInt = state.now
  def advance(seconds: BigInt): Unit = synchronized { held = held.copy(now = held.now + seconds.max(0)) }
  /** Delays for the sleeps to come, after those already set. */
  def delay(ds: BigInt*): Unit = synchronized { held = held.copy(delays = held.delays ++ ds) }
  def now: Flow[BigInt] = Flow.effect(time)
  def sleep(seconds: Term[BigInt]): Flow[Unit] = Flow.effect(seconds) { s =>
    synchronized { held = ClockState(held.now + s.max(0) + held.delays.headOption.getOrElse(BigInt(0)).max(0), held.delays.drop(1)) }
  }

/** A job run every `period` seconds (`Flow.every(60)(housekeeping)`). Each run is the job's flow, proven like any other;
  * that runs come every period is the scheduler's promise, an assumption the developer decides (a sleep may wake late).
  */
final class Every private[frflow] (val period: BigInt, val job: Flow[Unit]):
  /** One run as the scheduler makes it: the job, then a sleep of the period. */
  def once: Flow[Unit] = job.flatMap(_ => Flow.sleep(period))
  /** A run for each of `ticks`, in turn: the schedule as the proofs see it. Lean reads it as a `for` loop; a claim over
    * any number of runs is proven by induction on the list (`FrFlow.foldl_invariant`).
    */
  def runs[X](ticks: Term[List[X]]): Flow[Unit] = Flow.Each(ticks, (tick: Term[X]) => once)

  /** The scheduler, in `G`: `run` (the job's proven code, `knowledge.run[G](contract)(…)`), then a sleep of the period on
    * `clock`; `times` runs, or forever. Each run's start time goes to `started`, where the scheduler's assumption can be
    * checked: no gap between two starts longer than the period and what the job takes.
    */
  def schedule[G[_]](clock: Clock, times: Option[Int] = None, started: BigInt => Unit = _ => ())(run: () => G[Unit])(
      using G: cats.effect.kernel.Sync[G]): G[Unit] =
    import cats.syntax.all.*
    def step[A](f: Flow[A]): G[A] = Flows.run[G](Steps.of(f)._1, Map.empty, Map.empty, Nil).map(_.asInstanceOf[A])
    // Each run built when the one before has ended: forever is a loop, not a value built up front.
    def loop(left: Option[Int]): G[Unit] =
      if left.exists(_ <= 0) then G.unit
      else
        for
          t <- step(clock.now)
          _ <- G.delay(started(t))
          _ <- run()
          _ <- step(clock.sleep(Term.lit(period)))
          _ <- loop(left.map(_ - 1))
        yield ()
    loop(times)
