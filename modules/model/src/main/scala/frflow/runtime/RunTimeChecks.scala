package frflow
package runtime

import frflow.protocol.RunCheck
import java.util.SplittableRandom
import java.util.concurrent.atomic.AtomicLong

/** Which calls a run-time check checks. */
private[frflow] object RunTimeChecks:
  def chooser(c: RunCheck): () => Boolean = c match
    case RunCheck.EveryCall => () => true
    case RunCheck.Never     => () => false
    case RunCheck.Sampled(k, None) =>
      val calls = AtomicLong(0)
      () => calls.getAndIncrement() % k == 0
    case RunCheck.Sampled(k, Some(seed)) =>
      val random = SplittableRandom(seed)
      () => random.synchronized(random.nextInt(k) == 0)
