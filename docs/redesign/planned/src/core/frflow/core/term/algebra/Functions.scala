package frflow.core.term.algebra

import frflow.core.term.Bound

/** Functions and sharing (LNCS 7470 §3.2's `lam` and `app`): a named definition is a curried function applied one
  * argument at a time, whatever its arity; `let` names a value for its body.
  */
trait Functions[T[_]]:
  def lam[A, B](x: Bound[A])(f: T[A] => T[B]): T[A => B]
  def app[A, B](f: T[A => B], a: T[A]): T[B]
  def let[A, B](v: T[A], x: Bound[A])(body: T[A] => T[B]): T[B]
