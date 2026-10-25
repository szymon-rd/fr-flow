package frflow
package boundary

import java.lang.reflect.{InvocationHandler, Method, Proxy}
import scala.reflect.ClassTag

/** What proven code calls but cannot see: a plain trait of operations taking terms and returning flows. The
  * model names one value for it, as `Param` does for a term; production binds an implementation of the trait.
  * `db.load` calls the operation (an implicit conversion to the trait).
  */
final class Boundary[T] private (val name: String, val means: String, val cls: Class[T], private[frflow] val failure: Option[Term[?]]):
  /** The trait, recording each call as a step. */
  lazy val ops: T = Proxy.newProxyInstance(cls.getClassLoader, Array(cls), new InvocationHandler:
    def invoke(p: AnyRef, m: Method, args: Array[AnyRef] | Null): AnyRef =
      m.getName match
        case "toString" if m.getParameterCount == 0 => s"Boundary($name)"
        case "hashCode" if m.getParameterCount == 0 => Integer.valueOf(System.identityHashCode(p))
        case "equals" if m.getParameterCount == 1   => java.lang.Boolean.valueOf(p eq args.nn(0))
        case _ => Flow.Call[Any](Boundary.this, m, Option(args).fold(Nil)(_.toList.map(_.asInstanceOf[Term[?]])))
  ).asInstanceOf[T]
  /** Whether a call may fail (`Boundary.failing`). */
  def fails: Boolean = failure.isDefined
  /** The production implementation. */
  def bind(impl: T): Boundary.Bound = Boundary.Bound(this, impl)
  /** The operations, in the trait's order: what Lean's class declares. */
  private[frflow] def operations: List[Method] =
    cls.getMethods.toList.filter(m => classOf[Flow[?]].isAssignableFrom(m.getReturnType)).sortBy(_.getName)
  /** Lean's name of the class. */
  def lean: String = Names.ident(cls.getSimpleName)
  override def toString: String = name

object Boundary:
  def apply[T](name: String, means: String)(using ct: ClassTag[T]): Boundary[T] =
    val c = ct.runtimeClass.asInstanceOf[Class[T]]
    require(c.isInterface, s"FrFlow: the boundary $name is a trait of operations, not ${c.getName}")
    new Boundary(name, means, c, None)
  /** A boundary any call of which may fail with `error` (a store that is down, a mail server that refuses): a failed
    * call changes nothing of its model. The proofs hold for every pattern of failures (the world's `faults`); in
    * production, an exception from the implementation's call is that error.
    */
  def failing[T](name: String, means: String)(error: Term[?])(using ct: ClassTag[T]): Boundary[T] =
    val b = apply[T](name, means)
    new Boundary(name, means, b.cls, Some(error))
  given ops[T]: Conversion[Boundary[T], T] = _.ops
  final case class Bound(boundary: Boundary[?], impl: Any)
