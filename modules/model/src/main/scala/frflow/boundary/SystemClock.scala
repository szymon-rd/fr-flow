package frflow
package boundary

/** The computer's clock: seconds since 1970, and the thread put to sleep. Outside the proofs: assumed, not tested. */
object SystemClock extends Clock:
  def now: Flow[BigInt] = Flow.effect(BigInt(System.currentTimeMillis / 1000))
  def sleep(seconds: Term[BigInt]): Flow[Unit] = Flow.effect(seconds)(s => if s > 0 then Thread.sleep((s * 1000).toLong))
