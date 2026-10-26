package frflow.core.term.algebra

/** Truth values, as an algebra over the representation `T` (LNCS 7470 §2.1: a term is what its operations build, for
  * any interpreter; §3.2's `Symantics`, split by meaning as §2.2 extends a language).
  */
trait Logic[T[_]]:
  def bool(b: Boolean): T[Boolean]
  def and(a: T[Boolean], b: T[Boolean]): T[Boolean]
  def or(a: T[Boolean], b: T[Boolean]): T[Boolean]
  def not(a: T[Boolean]): T[Boolean]
  def implies(a: T[Boolean], b: T[Boolean]): T[Boolean]
  def cond[A](c: T[Boolean], ifTrue: T[A], ifFalse: T[A]): T[A]
