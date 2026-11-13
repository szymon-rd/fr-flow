package frflow.core.term.optimize

import frflow.core.expr.{Binder, Value}
import frflow.core.term.{Annotation, Bound, Ext}
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A term, and whether writing it where it is read computes nothing twice: a variable, a small constant, a pair of
  * such.
  */
final case class Atomic[T[_], A](t: T[A], atom: Boolean = false)

/** A `let` of what may be written where it is read names nothing: its body reads the value itself. A `let` of
  * anything computed stays, so nothing is computed twice.
  */
final class Inlined[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Atomic[T, a]]:
  private type K[A] = Atomic[T, A]
  protected def fwd[A](t: T[A]): K[A] = Atomic(t)
  protected def bwd[A](u: K[A]): T[A] = u.t
  /** A variable a binder gives its body: an atom. */
  override protected def body[A, B](p: K[A] => K[B]): T[A] => T[B] = v => p(Atomic(v, atom = true)).t

  override def bool(b: Boolean): K[Boolean] = Atomic(base.bool(b), atom = true)
  override def nil[A](elem: Ty): K[List[A]] = Atomic(base.nil(elem), atom = true)
  override def free[A](x: Binder): K[A] = Atomic(base.free(x), atom = true)
  override def lit[A](a: A, value: Value, ty: Ty): K[A] = Atomic(base.lit(a, value, ty), value match
    case Value.Bool(_) | Value.Num(_) | Value.Str(_) | Value.Unit | Value.Many(Nil) => true
    case _                                                                         => false)
  override def pair[A, B](a: K[A], b: K[B]): K[(A, B)] = Atomic(base.pair(a.t, b.t), a.atom && b.atom)
  override def let[A, B](v: K[A], x: Bound[A])(b: K[A] => K[B]): K[B] = if v.atom then b(v) else super.let(v, x)(b)
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Atomic[T, a]]] = None

object Inlined:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Atomic[T, a]](Inlined(s)).t
