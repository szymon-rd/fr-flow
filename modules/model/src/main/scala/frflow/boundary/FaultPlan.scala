package frflow
package boundary

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
