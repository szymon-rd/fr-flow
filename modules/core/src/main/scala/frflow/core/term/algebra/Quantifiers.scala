package frflow.core.term.algebra

import frflow.core.term.Bound

/** `∀` and `∃` over every value of a type, and `always` over every value that can occur (owner §15: of a domain
  * type, every value that can be made; of the worlds, every state the models reach); the body a host function
  * (higher-order abstract syntax, LNCS 7470 §3.2).
  */
trait Quantifiers[T[_]]:
  def forall[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def exists[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
  def always[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean]
