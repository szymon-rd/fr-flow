package frflow.runtime.check

import frflow.core.code.RunCheck
import java.util.concurrent.atomic.AtomicLong
import java.util.SplittableRandom

/** Which calls a service checks, as today's `RunTimeChecks.chooser`: every call, none, one in `k` counted, or one in
  * `k` drawn from the seed. A sampled service's counter (an `AtomicLong`) or generator (a `SplittableRandom` used
  * under its lock) is shared mutable state, shared by that service's calls, as `AssumptionWatch.held` is.
  */
object Sampling:
  def of(c: RunCheck): () => Boolean = c match
    case RunCheck.EveryCall              => () => true
    case RunCheck.Never                  => () => false
    case RunCheck.Sampled(k, None)       =>
      val calls = AtomicLong(0)
      () => calls.getAndIncrement() % k == 0
    case RunCheck.Sampled(k, Some(seed)) =>
      val random = SplittableRandom(seed)
      () => random.synchronized(random.nextInt(k) == 0)
