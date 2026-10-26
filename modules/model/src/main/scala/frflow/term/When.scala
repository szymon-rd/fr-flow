package frflow
package term

/** `when(booked)(held :+ request).otherwise(held)`: the first term when the condition holds, else the second. Lean's
  * `if … then … else …`.
  */
final class When[A] private[frflow] (condition: Term[Boolean], ifTrue: Term[A]):
  def otherwise(ifFalse: Term[A]): Term[A] = condition.fold(ifTrue, ifFalse)

object When:
  def when[A](condition: Term[Boolean])(ifTrue: Term[A]): When[A] = new When(condition, ifTrue)
