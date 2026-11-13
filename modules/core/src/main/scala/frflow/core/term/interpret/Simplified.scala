package frflow.core.term.interpret

import frflow.core.expr.{Binder, Value}
import frflow.core.term.{Annotation, Bound, Ext, Selector}
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty

/** A term with what is known of it where it is written out: the two parts of a pair just made, a truth value, a
  * list with no member; and whether writing it twice computes nothing twice (`atom`: a variable, a small constant).
  */
final case class Shaped[T[_], A](t: T[A], parts: Option[(Shaped[T, Any], Shaped[T, Any])] = None,
    truth: Option[Boolean] = None, empty: Boolean = false, atom: Boolean = false):
  /** Whether it may be written where it is read: an atom, or a pair of what may be. */
  def copied: Boolean = atom || parts.exists((a, b) => a.copied && b.copied)

/** Code with what it computes of a shape it has just built taken out: an optimization by `fwd` and `bwd` (Kiselyov's
  * course, the optimization pages; `Forward`). The representation is the term with its known shape (`Shaped`):
  * `fwd` knows nothing of a term, `bwd` forgets what is known, so `bwd` of `fwd` is the term. A part of a pair just
  * made is that part; an `if` on a truth value written out is its branch, and so the connectives; a list joined
  * with none is itself; a `let` of what may be written where it is read names nothing, and one that stays lets its
  * body know its parts. The code compiled from a class is full of these: the state and the result a member gives
  * are a pair, taken apart where the next step begins.
  */
final class Simplified[T[_]](protected val base: Sym[T]) extends Forward[T, [a] =>> Shaped[T, a]]:
  private type K[A] = Shaped[T, A]
  protected def fwd[A](t: T[A]): K[A] = Shaped(t)
  protected def bwd[A](u: K[A]): T[A] = u.t
  /** A variable a binder gives its body: an atom. */
  override protected def body[A, B](p: K[A] => K[B]): T[A] => T[B] = v => p(Shaped(v, atom = true)).t

  override def bool(b: Boolean): K[Boolean] = Shaped(base.bool(b), truth = Some(b), atom = true)
  override def not(a: K[Boolean]): K[Boolean] = a.truth.fold(super.not(a))(b => bool(!b))
  override def and(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.truth, b.truth) match
    case (Some(true), _)                   => b
    case (_, Some(true))                   => a
    case (Some(false), _) | (_, Some(false)) => bool(false)
    case _                                 => super.and(a, b)
  override def or(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.truth, b.truth) match
    case (Some(false), _)                => b
    case (_, Some(false))                => a
    case (Some(true), _) | (_, Some(true)) => bool(true)
    case _                               => super.or(a, b)
  override def cond[A](c: K[Boolean], t: K[A], e: K[A]): K[A] = c.truth.fold(super.cond(c, t, e))(if _ then t else e)

  override def lit[A](a: A, value: Value, ty: Ty): K[A] = value match
    case Value.Bool(b)                           => bool(b).asInstanceOf[K[A]] // a truth value is a `Boolean`
    case Value.Num(_) | Value.Str(_) | Value.Unit => Shaped(base.lit(a, value, ty), atom = true)
    case Value.Many(Nil)                         => Shaped(base.lit(a, value, ty), empty = true, atom = true)
    case _                                       => super.lit(a, value, ty)
  override def nil[A](elem: Ty): K[List[A]] = Shaped(base.nil(elem), empty = true, atom = true)
  override def append[A](xs: K[List[A]], ys: K[List[A]]): K[List[A]] =
    if xs.empty then ys else if ys.empty then xs else super.append(xs, ys)

  override def pair[A, B](a: K[A], b: K[B]): K[(A, B)] =
    // the parts are kept at any type: `field` gives each back at the type its selector reads
    Shaped(base.pair(a.t, b.t), parts = Some((a.asInstanceOf[K[Any]], b.asInstanceOf[K[Any]])))
  override def field[R, F](r: K[R], s: Selector[R, F]): K[F] = r.parts match
    case Some((a, b)) if s.record == Selector.pair => (if s.index == 0 then a else b).asInstanceOf[K[F]]
    case _                                         => super.field(r, s)

  override def free[A](x: Binder): K[A] = Shaped(base.free(x), atom = true)
  override def let[A, B](v: K[A], x: Bound[A])(b: K[A] => K[B]): K[B] =
    if v.copied then b(v) else fwd(base.let(v.t, x)(named => b(known(named, v, x.ty)).t))
  override def noted[A](n: Annotation, t: K[A]): K[A] = t.copy(t = base.noted(n, t.t))
  override def extension[E[_[_]]](key: Ext[E]): Option[E[[a] =>> Shaped[T, a]]] = None

  /** A value a `let` named, as its body reads it: the name, and of a pair each part that may be written where it
    * is read; any other part is read off the name.
    */
  private def known[A](named: T[A], v: K[A], ty: Ty): K[A] = (v.parts, ty) match
    case (Some((a, b)), Ty.TupleOf(List(left, right))) =>
      val pair = named.asInstanceOf[T[(Any, Any)]] // what has parts is a pair
      val first = if a.copied then a else Shaped(base.field(pair, Selector.first[Any, Any](left)), atom = true)
      val second = if b.copied then b else Shaped(base.field(pair, Selector.second[Any, Any](right)), atom = true)
      Shaped(named, parts = Some((first, second)), atom = true)
    case _                                             => Shaped(named, atom = true)

object Simplified:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[[a] =>> Shaped[T, a]](Simplified(s)).t
