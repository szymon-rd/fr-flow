package frflow.core.term.algebra

import frflow.core.term.Bound
import frflow.core.ty.Ty

/** Optional values: one, none of a type, and their eliminator (`o.fold(ifNone)(x => ifSome)`); whether none or the
  * one meets a rule (`optionAll`, Scala's `o.forall`), whether one does (`optionAny`, `o.exists`), whether there is
  * one, and the one or a default.
  */
trait Options[T[_]]:
  def some[A](a: T[A]): T[Option[A]]
  def none[A](elem: Ty): T[Option[A]]
  def foldOption[A, R](o: T[Option[A]], ifNone: T[R], x: Bound[A])(ifSome: T[A] => T[R]): T[R]
  def optionAll[A](o: T[Option[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def optionAny[A](o: T[Option[A]], x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def isDefined[A](o: T[Option[A]]): T[Boolean]
  def getOrElse[A](o: T[Option[A]], default: T[A]): T[A]
