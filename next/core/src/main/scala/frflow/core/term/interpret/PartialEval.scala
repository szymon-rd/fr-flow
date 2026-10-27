package frflow.core.term.interpret

import frflow.core.expr.Value
import frflow.core.term.*
import frflow.core.ty.{NumKind, Ty}

/** Constant folding as an interpreter transformer over any interpreter `s` (Carette, Kiselyov and Shan, JFP 2009, §4,
  * the partial evaluator: each term's static value when known, and its dynamic term): `true && p` is `p` before Lean
  * or Scala sees it. A known left operand decides `&&`, `||` and `implies`; a known right one only drops itself, so an
  * operand that has no Scala value (a quantifier) is still met in the same order. A field of a known record is known.
  * Operations it cannot fold are `s`'s (`Forward`).
  */
final class PartialEval[T[_]](s: Sym[T]) extends Forward[T, [a] =>> Known[T, a]]:
  private type K[A] = Known[T, A]
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): K[A] = Known(None, t)
  protected def bwd[A](u: K[A]): T[A] = u.later

  override def bool(b: Boolean): K[Boolean] = Known(Some(b), s.bool(b))
  override def and(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.now, b.now) match
    case (Some(x), _)    => if x then b else a
    case (_, Some(true)) => a
    case _               => super.and(a, b)
  override def or(a: K[Boolean], b: K[Boolean]): K[Boolean] = (a.now, b.now) match
    case (Some(x), _)     => if x then a else b
    case (_, Some(false)) => a
    case _                => super.or(a, b)
  override def implies(a: K[Boolean], b: K[Boolean]): K[Boolean] =
    a.now.fold(super.implies(a, b))(if _ then b else bool(true))
  override def not(a: K[Boolean]): K[Boolean] = a.now.fold(super.not(a))(v => bool(!v))
  override def cond[A](c: K[Boolean], t: K[A], e: K[A]): K[A] = c.now.fold(super.cond(c, t, e))(if _ then t else e)
  override def eq[A](a: K[A], b: K[A]): K[Boolean] = folded(a, b)(_ == _)(bool)(super.eq)
  override def add(a: K[BigInt], b: K[BigInt]): K[BigInt] = folded(a, b)(_ + _)(num)(super.add)
  override def sub(a: K[BigInt], b: K[BigInt]): K[BigInt] = folded(a, b)(_ - _)(num)(super.sub)
  override def lt(a: K[BigInt], b: K[BigInt]): K[Boolean] = folded(a, b)(_ < _)(bool)(super.lt)
  override def le(a: K[BigInt], b: K[BigInt]): K[Boolean] = folded(a, b)(_ <= _)(bool)(super.le)
  override def lit[A](a: A, value: Value, ty: Ty): K[A] = Known(Some(a), s.lit(a, value, ty))
  override def noted[A](n: Annotation, t: K[A]): K[A] = Known(t.now, s.noted(n, t.later))
  override def field[R, F](r: K[R], sel: Selector[R, F]): K[F] = Known(r.now.map(sel.get), s.field(r.later, sel))

  /** Both operands known: the value, as `constant` makes it; otherwise the operation on the operands' terms. */
  private def folded[A, B, R](a: K[A], b: K[B])(f: (A, B) => R)(constant: R => K[R])(otherwise: (K[A], K[B]) => K[R])
      : K[R] =
    a.now.zip(b.now).fold(otherwise(a, b))((x, y) => constant(f(x, y)))

  private def num(n: BigInt): K[BigInt] = Known(Some(n), s.lit(n, Value.Num(n), Ty.Num(NumKind.Big)))

object PartialEval:
  def of[T[_], A](t: Final[A], s: Sym[T]): T[A] = t[[a] =>> Known[T, a]](PartialEval(s)).later
