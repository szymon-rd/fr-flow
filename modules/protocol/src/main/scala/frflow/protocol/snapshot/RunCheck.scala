package frflow.protocol
package snapshot

import io.circe.Codec

/** How a contract's code is checked where it runs (`service`): a decision of the developer's, or the default for its kind. */
enum RunCheck derives Codec.AsObject:
  /** Every call's result is checked: one that breaks the check is never returned. */
  case EveryCall
  /** One call in `oneIn`: every `oneIn`-th (the first included), or, with a seed, calls drawn at that rate. */
  case Sampled(oneIn: Int, seed: Option[Long] = None)
  /** Not checked: the running code is the code Lean proves. Assumptions about the values it runs with still are. */
  case Never
  def describe: String = this match
    case EveryCall          => "every call"
    case Sampled(n, None)    => s"one call in $n (every ${n}th, the first included)"
    case Sampled(n, Some(s)) => s"one call in $n, drawn at random (seed $s)"
    case Never              => "not checked"
