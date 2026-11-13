package frflow.core.term.optimize

import frflow.core.expr.Value
import frflow.core.term.{Annotation, Ext}
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A term, and whether it is a list written out with no member. */
final case class Listed[T[_], A](t: T[A], empty: Boolean = false)

/** A list joined with one that has no member is itself: the traces a member's steps are kept in start with none. */
final class Joined[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Listed[T, a]]:
  private type K[A] = Listed[T, A]
  protected def fwd[A](t: T[A]): K[A] = Listed(t)
  protected def bwd[A](u: K[A]): T[A] = u.t

  override def nil[A](elem: Ty): K[List[A]] = Listed(base.nil(elem), empty = true)
  override def lit[A](a: A, value: Value, ty: Ty): K[A] = Listed(base.lit(a, value, ty), value == Value.Many(Nil))
  override def append[A](xs: K[List[A]], ys: K[List[A]]): K[List[A]] =
    if xs.empty then ys else if ys.empty then xs else super.append(xs, ys)
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Listed[T, a]]] = None

object Joined:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Listed[T, a]](Joined(s)).t
