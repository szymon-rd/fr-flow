package frflow
package boundary

/** The clock as the proofs see it: the time in the state, a sleep moving it on by the time asked and the next delay.
  * Nothing else moves it: a flow that reads the clock twice, with no sleep between, reads the same time. That the clock
  * never goes backwards is what the developer assumes of it (`Node.assumption(Clock.boundary)(ClockModel)(…)`).
  */
object ClockModel extends Clock, StateModel[ClockState]:
  def now: Flow[BigInt] = state.get.map(c => c.now)
  def sleep(seconds: Term[BigInt]): Flow[Unit] =
    state.update(c => ClockState(c.now + seconds.max(0) + c.delays.headOption.getOrElse(0).max(0), c.delays.drop(1)))
