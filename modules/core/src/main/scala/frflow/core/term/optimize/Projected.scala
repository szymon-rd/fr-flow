package frflow.core.term.optimize

import frflow.core.expr.{Binder, Value}
import frflow.core.term.{Annotation, Bound, Ext, Selector}
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A term with what is known of it where it is read: the two parts of a pair, just made or named by a `let`; and
  * whether writing it twice computes nothing twice (`atom`: a variable, a small constant).
  */
final case class Paired[T[_], A](t: T[A], parts: Option[(Paired[T, Any], Paired[T, Any])] = None,
    atom: Boolean = false):
  /** Whether it may be written where it is read: an atom, or a pair of what may be. */
  def copied: Boolean = atom || parts.exists((a, b) => a.copied && b.copied)

/** A part read of a pair is that part, where the pair was made or through the name a `let` gave it: the pass that
  * takes pairs apart (the result and the state a member gives are a pair, named, and taken apart where the next
  * step begins). A `let` of what may be written where it is read names nothing; one that stays lets its body know
  * its parts: each part that may be written is, and any other is read off the name, so nothing is computed twice.
  * Rocq's proofs run the code step by step, and a part known where it is read is a step they do not take.
  */
final class Projected[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Paired[T, a]]:
  private type K[A] = Paired[T, A]
  protected def fwd[A](t: T[A]): K[A] = Paired(t)
  protected def bwd[A](u: K[A]): T[A] = u.t
  /** A variable a binder gives its body: an atom. */
  override protected def body[A, B](p: K[A] => K[B]): T[A] => T[B] = v => p(Paired(v, atom = true)).t

  override def bool(b: Boolean): K[Boolean] = Paired(base.bool(b), atom = true)
  override def nil[A](elem: Ty): K[List[A]] = Paired(base.nil(elem), atom = true)
  override def free[A](x: Binder): K[A] = Paired(base.free(x), atom = true)
  override def lit[A](a: A, value: Value, ty: Ty): K[A] = Paired(base.lit(a, value, ty), atom = value match
    case Value.Bool(_) | Value.Num(_) | Value.Str(_) | Value.Unit | Value.Many(Nil) => true
    case _                                                                         => false)

  override def pair[A, B](a: K[A], b: K[B]): K[(A, B)] =
    // the parts are kept at any type: `field` gives each back at the type its selector reads
    Paired(base.pair(a.t, b.t), parts = Some((a.asInstanceOf[K[Any]], b.asInstanceOf[K[Any]])))
  override def field[R, F](r: K[R], s: Selector[R, F]): K[F] = r.parts match
    case Some((a, b)) if s.record == Selector.pair => (if s.index == 0 then a else b).asInstanceOf[K[F]]
    case _                                         => super.field(r, s)
  override def let[A, B](v: K[A], x: Bound[A])(b: K[A] => K[B]): K[B] =
    if v.copied then b(v) else fwd(base.let(v.t, x)(named => b(known(named, v, x.ty)).t))
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Paired[T, a]]] = None

  /** A value a `let` named, as its body reads it: the name, and of a pair each part that may be written where it
    * is read; any other part is read off the name.
    */
  private def known[A](named: T[A], v: K[A], ty: Ty): K[A] = (v.parts, ty) match
    case (Some((a, b)), Ty.TupleOf(List(left, right))) =>
      val pair = named.asInstanceOf[T[(Any, Any)]] // what has parts is a pair
      val first = if a.copied then a else Paired(base.field(pair, Selector.first[Any, Any](left)), atom = true)
      val second = if b.copied then b else Paired(base.field(pair, Selector.second[Any, Any](right)), atom = true)
      Paired(named, parts = Some((first, second)), atom = true)
    case _                                             => Paired(named, atom = true)

object Projected:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Paired[T, a]](Projected(s)).t
