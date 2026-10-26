package frflow.core.term.algebra

import frflow.core.expr.Binder

/** A variable bound outside the term: a lambda's input, at its level, or a recorded program's step. */
trait Variables[T[_]]:
  def free[A](x: Binder): T[A]
