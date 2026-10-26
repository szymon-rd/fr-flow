package frflow.dsl.flow

import frflow.core.name.BoundaryName
import scala.reflect.ClassTag

/** What proven code calls but cannot see: a trait of operations whose calls are recorded as `Flow.Call`. */
trait Boundary[T]:
  def name: BoundaryName
  def means: String
  def ops: BoundaryOps[T]
  def bind(impl: T): Bound = Bound(name, ops.ops, ops.call(impl, _, _))

object Boundary:
  def apply[T: BoundaryOps: ClassTag](name: String, means: String): Boundary[T] & T = ???
