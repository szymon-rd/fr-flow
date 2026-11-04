package frflow.core.term.algebra

import frflow.core.term.{Constructor, Selector}

/** Records and cases: a constructor as a curried function (applied with `Functions.app`), a field read and a field
  * replaced by a typed selector (Scala's own getter and copy, derived per type), and a pair.
  */
trait Records[T[_]]:
  def construct[F](c: Constructor[F]): T[F]
  def field[R, F](r: T[R], s: Selector[R, F]): T[F]
  def copy[R, F](r: T[R], s: Selector[R, F], v: T[F]): T[R]
  def pair[A, B](a: T[A], b: T[B]): T[(A, B)]
