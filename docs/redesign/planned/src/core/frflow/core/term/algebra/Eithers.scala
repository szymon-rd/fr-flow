package frflow.core.term.algebra

import frflow.core.term.Bound
import frflow.core.ty.Ty

/** An error or a value (Lean's `Except`): the two injections, typed by the whole, and their eliminator. */
trait Eithers[T[_]]:
  def left[E, A](e: T[E], ty: Ty): T[Either[E, A]]
  def right[E, A](a: T[A], ty: Ty): T[Either[E, A]]
  def foldEither[E, A, R](v: T[Either[E, A]], e: Bound[E], a: Bound[A])(onLeft: T[E] => T[R], onRight: T[A] => T[R])
      : T[R]
