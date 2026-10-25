package frflow
package boundary

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
