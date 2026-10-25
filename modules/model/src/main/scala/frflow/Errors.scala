package frflow

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

/** A flow that failed in production with `error` (a value of the flow's error type): the exception `run` fails with
  * when no `handleErrorWith` handles it.
  */
final case class FlowFailed(error: Any) extends RuntimeException(s"the flow failed with ${Example.show(error)}", null, false, false)

/** A run on the models that failed with `error`: what an example of a flow gives as its result for a run that fails
  * (`expect(request, before.failing(true), Failed(Failure.StoreUnavailable), before, "the store is down")`).
  */
final case class Failed(error: Any):
  override def toString: String = s"Failed(${Example.show(error)})"

/** Failures injected into a failing boundary's implementation, as a world's `faults` say: each call of the boundaries
  * the plan wraps takes the next fault, in order, and `true` makes it throw before the implementation is called. What
  * the generated tests and a scripted session use to fail a store at a chosen step.
  */
final class FaultPlan(faults: List[Boolean]):
  private val left = java.util.concurrent.atomic.AtomicReference(faults)
  /** The faults not yet taken. */
  def remaining: List[Boolean] = left.get
  /** Whether the next call will fail, taking its fault. */
  private[frflow] def next(): Boolean = left.getAndUpdate(_.drop(1)).headOption.contains(true)
  /** `impl`, failing as the plan says on each call of an operation of the boundary's trait. */
  def apply[T](b: Boundary[T], impl: T): T =
    java.lang.reflect.Proxy.newProxyInstance(b.cls.getClassLoader, Array(b.cls), (p: AnyRef, m: java.lang.reflect.Method, args: Array[AnyRef] | Null) =>
      if classOf[Flow[?]].isAssignableFrom(m.getReturnType) && next() then
        throw IllegalStateException(s"${b.name} is down (a fault injected)")
      try m.invoke(impl, (if args == null then Array.empty[AnyRef] else args)*)
      catch case e: java.lang.reflect.InvocationTargetException => throw e.getCause
    ).asInstanceOf[T]
  /** Each failing boundary's implementation in `impls` wrapped. */
  def all(impls: Map[Boundary[?], Any]): Map[Boundary[?], Any] =
    impls.map((b, i) => if b.fails then b -> apply(b.asInstanceOf[Boundary[Any]], i) else b -> i)
