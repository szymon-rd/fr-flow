package frflow.core.term.algebra

import frflow.core.term.Bound
import frflow.core.ty.Ty

/** Optional values: one, none of a type, and their eliminator (`o.fold(ifNone)(x => ifSome)`). */
trait Options[T[_]]:
  def some[A](a: T[A]): T[Option[A]]
  def none[A](elem: Ty): T[Option[A]]
  def foldOption[A, R](o: T[Option[A]], ifNone: T[R], x: Bound[A])(ifSome: T[A] => T[R]): T[R]
