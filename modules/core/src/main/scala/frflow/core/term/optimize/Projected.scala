package frflow.core.term.optimize

import frflow.core.term.{Annotation, Ext, Selector}
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Sym}

/** A term, and of a pair just made its two parts, as the next interpreter has them. */
final case class Paired[T[_], A](t: T[A], parts: Option[(T[Any], T[Any])] = None)

/** A part read of a pair just made is that part: the pass that takes pairs apart where they are built (the result
  * and the state a member gives, read where the next step begins). The state is the pair's two parts and no more;
  * a part that is itself a pair is known to the same pass run again (`Optimized`).
  */
final class Projected[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Paired[T, a]]:
  private type K[A] = Paired[T, A]
  protected def fwd[A](t: T[A]): K[A] = Paired(t)
  protected def bwd[A](u: K[A]): T[A] = u.t

  override def pair[A, B](a: K[A], b: K[B]): K[(A, B)] =
    // the parts are kept at any type: `field` gives each back at the type its selector reads
    Paired(base.pair(a.t, b.t), Some((a.t.asInstanceOf[T[Any]], b.t.asInstanceOf[T[Any]])))
  override def field[R, F](r: K[R], s: Selector[R, F]): K[F] = r.parts match
    case Some((a, b)) if s.record == Selector.pair => fwd((if s.index == 0 then a else b).asInstanceOf[T[F]])
    case _                                         => super.field(r, s)
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Paired[T, a]]] = None

object Projected:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Paired[T, a]](Projected(s)).t
