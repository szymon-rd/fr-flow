package frflow.core.consistency

import frflow.core.expr.Value
import frflow.core.term.{Annotation, Bound, Final, Sym}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.term.interpret.Forward

/** The witness a defining formula gives (owner §18): of `∀ xs, s(xs) = e` the function `fun xs => e`, of a bound
  * `s(xs) ≤ e` the bound itself, of `s(xs) < e` one less. A transformer that keeps, beside each term, the side
  * `picked` of its relation, wrapped in a `lam` per leading `forall`. `consistency.Equations` read the shape off the
  * IR first, so only the leading `forall`s and the relation are met here.
  */
final class Defining[T[_]](s: Sym[T], picked: Picked) extends Forward[T, [a] =>> Sided[T, a]]:
  protected def base: Sym[T] = s
  protected def fwd[A](t: T[A]): Sided[T, A] = Sided(t, t.asInstanceOf[T[Any]]) // a leaf is no relation: unused
  protected def bwd[A](u: Sided[T, A]): T[A] = u.whole

  override def noted[A](n: Annotation, t: Sided[T, A]): Sided[T, A] = Sided(s.noted(n, t.whole), t.witness)

  override def forall[A](x: Bound[A])(p: Sided[T, A] => Sided[T, Boolean]): Sided[T, Boolean] =
    Sided(s.forall(x)(v => p(fwd(v)).whole), s.lam(x)(v => p(fwd(v)).witness).asInstanceOf[T[Any]])

  override def eq[A](a: Sided[T, A], b: Sided[T, A]): Sided[T, Boolean] = related(s.eq(a.whole, b.whole), a, b)
  override def le(a: Sided[T, BigInt], b: Sided[T, BigInt]): Sided[T, Boolean] = related(s.le(a.whole, b.whole), a, b)
  override def lt(a: Sided[T, BigInt], b: Sided[T, BigInt]): Sided[T, Boolean] = related(s.lt(a.whole, b.whole), a, b)

  private def related[A](whole: T[Boolean], a: Sided[T, A], b: Sided[T, A]): Sided[T, Boolean] =
    val (side, by) = picked match
      case Picked.Left(k)  => (a.whole, k)
      case Picked.Right(k) => (b.whole, k)
    Sided(whole, by match
      case 0 => side.asInstanceOf[T[Any]]
      case k => shifted(side.asInstanceOf[T[BigInt]], k).asInstanceOf[T[Any]]) // an order's sides are `BigInt`

  private def shifted(v: T[BigInt], k: Int): T[BigInt] =
    if k > 0 then s.add(v, one) else s.sub(v, one)
  private def one: T[BigInt] = s.lit(BigInt(1), Value.Num(1), Ty.Num(NumKind.Big))

object Defining:
  /** The witness `rule` gives, as a term of every interpreter. */
  def of(rule: Final[Boolean], picked: Picked): Final[Any] =
    [T[_]] => (s: Sym[T]) => rule[[a] =>> Sided[T, a]](Defining(s, picked)).witness
