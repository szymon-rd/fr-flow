package frflow
package boundary

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
