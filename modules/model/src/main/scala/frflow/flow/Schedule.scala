package frflow
package flow

/** How a flow is tried again (`f.retry[E](schedule)`), as a value: the waits before each retry, in seconds. A flow
  * retried with `Schedule(List(1, 2, 4))` is tried at most four times: at once, then after 1, 2 and 4 more seconds.
  */
final case class Schedule(waits: List[BigInt]):
  /** How many times the flow is tried at most. */
  def attempts: Int = waits.size + 1
  override def toString: String =
    if waits.isEmpty then "once" else s"$attempts tries, waiting ${waits.mkString(", ")} s between them"

object Schedule:
  /** Tried once: no retry. */
  val once: Schedule = Schedule(Nil)
  /** `retries` retries, each after the same wait. */
  def fixed(seconds: BigInt, retries: Int): Schedule = Schedule(List.fill(retries)(seconds))
  /** `retries` retries, the first after `first` seconds and each wait `factor` times the one before (backoff). */
  def exponential(first: BigInt, retries: Int, factor: Int = 2): Schedule =
    Schedule(List.tabulate(retries)(i => first * BigInt(factor).pow(i)))
