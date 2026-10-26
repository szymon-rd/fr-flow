package frflow.core.term.algebra

/** Equality of two values of one type: structural in Scala, `=` in Lean. */
trait Equality[T[_]]:
  def eq[A](a: T[A], b: T[A]): T[Boolean]
