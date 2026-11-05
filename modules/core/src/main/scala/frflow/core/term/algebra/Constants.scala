package frflow.core.term.algebra

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** A constant: the host value for interpreters that compute, and its `Value` and type for those that print. */
trait Constants[T[_]]:
  def lit[A](a: A, value: Value, ty: Ty): T[A]
