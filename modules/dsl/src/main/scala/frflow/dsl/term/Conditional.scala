package frflow.dsl.term

import frflow.core.term.Sym

/** `when(c)(a)`, waiting for its other branch: `.otherwise(b)` is Lean's `if c then a else b`. */
final class Conditional[A](condition: Term[Boolean], ifTrue: Term[A]):
  def otherwise(ifFalse: Term[A]): Term[A] =
    Term[A]([T[_]] => (s: Sym[T]) => s.cond(condition.run(s), ifTrue.run(s), ifFalse.run(s)))(using ifTrue.leanType)
