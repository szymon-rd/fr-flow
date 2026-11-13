package frflow.core.term.optimize

import frflow.core.expr.Value
import frflow.core.term.{Annotation, Ext}
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A term, and its truth value where it is written out. */
final case class Truth[T[_], A](t: T[A], known: Option[Boolean] = None)

/** Truth values written out are propagated: an `if` on one is its branch, and a connective one side of which is
  * known is the other side, or known itself.
  */
final class Decided[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Truth[T, a]]:
  private type K[A] = Truth[T, A]
  protected def fwd[A](t: T[A]): K[A] = Truth(t)
  protected def bwd[A](u: K[A]): T[A] = u.t

  override def bool(b: Boolean): K[Boolean] = Truth(base.bool(b), Some(b))
  override def lit[A](a: A, value: Value, ty: Ty): K[A] = value match
    case Value.Bool(b) => bool(b).asInstanceOf[K[A]] // a truth value is a `Boolean`
    case _             => super.lit(a, value, ty)
  override def not(a: K[Boolean]): K[Boolean] = a.known.fold(super.not(a))(b => bool(!b))
  override def and(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.known, b.known) match
    case (Some(true), _)                     => b
    case (_, Some(true))                     => a
    case (Some(false), _) | (_, Some(false)) => bool(false)
    case _                                   => super.and(a, b)
  override def or(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.known, b.known) match
    case (Some(false), _)                  => b
    case (_, Some(false))                  => a
    case (Some(true), _) | (_, Some(true)) => bool(true)
    case _                                 => super.or(a, b)
  override def implies(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.known, b.known) match
    case (Some(true), _)                    => b
    case (Some(false), _) | (_, Some(true)) => bool(true)
    case _                                  => super.implies(a, b)
  override def cond[A](c: K[Boolean], t: K[A], e: K[A]): K[A] = c.known.fold(super.cond(c, t, e))(if _ then t else e)
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Truth[T, a]]] = None

object Decided:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Truth[T, a]](Decided(s)).t
