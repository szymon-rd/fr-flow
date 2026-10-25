package frflow
package boundary

/** What the clock's model holds: the time now, in seconds, and the delays still to come. A sleep of `d` seconds wakes
  * `d` seconds later plus the next delay (a delay below zero counts as zero), which the proofs do not know: a flow is
  * proven for every start time and every list of delays, so for every wake-up that is not early.
  */
final case class ClockState(now: BigInt, delays: List[BigInt])

object ClockState extends Data[ClockState]
