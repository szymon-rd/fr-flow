package frflow.core.term.interpret

import frflow.core.term.{Bound, Final, Sym}

/** A formula with what always holds as hypotheses: below each `forall`, the guards of its variable's type, in order,
  * imply the body (below an `exists`, they are conjuncts). A transformer (`Forward`, the identity on `T`) that
  * changes the quantifiers only, so every `always` holds of every value a statement is about without being written
  * in it.
  */
final class Guarded[T[_]](s: Sym[T], guards: List[Guard]) extends Forward[T, T]:
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): T[A] = t
  protected def bwd[A](u: T[A]): T[A] = u

  override def forall[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] =
    s.forall(x)(v => hypotheses(x, v).foldRight(p(v))(s.implies))
  override def exists[A](x: Bound[A])(p: T[A] => T[Boolean]): T[Boolean] =
    s.exists(x)(v => hypotheses(x, v).foldRight(p(v))(s.and))

  private def hypotheses[A](x: Bound[A], v: T[A]): List[T[Boolean]] =
    guards.flatMap(_.of[T, A](x.ty, s)).map(_(v))

object Guarded:
  def of[A](t: Final[A], guards: List[Guard]): Final[A] = [T[_]] => (s: Sym[T]) => t[T](Guarded(s, guards))
