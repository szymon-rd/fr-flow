package frflow.eval.term

import frflow.core.{Booking, Lang}
import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, SymbolName}
import frflow.core.term.Bound
import frflow.core.term.interpret.Forward
import frflow.core.term.language.{Final, Stated, Sym}
import frflow.core.ty.Ty
import frflow.proof.lean.laws.{Event, MoreTerms}

/** An interpreter over `base` that gives each symbol the law generators name (core's `Terms`, proof's `MoreTerms`) a
  * closed value of its type, built in the algebras: a generated term made closed, the same term for the evaluator and
  * for Lean's printer. A symbol it has no value for stays a symbol.
  */
final class Closed[T[_]](protected val base: Sym[T]) extends Forward[T, T]:
  protected def fwd[A](t: T[A]): T[A] = t
  protected def bwd[A](u: T[A]): T[A] = u
  override def param[A](name: SymbolName, ty: Ty): T[A] =
    // each value is built at the symbol's own type, which the generators gave it with this name
    Closed.values.get(name.value).fold(base.param[A](name, ty)) { case v: Stated[a] =>
      v.run[T](this).asInstanceOf[T[A]] }

object Closed:
  def of[A](t: Final[A]): Final[A] = [T[_]] => (s: Sym[T]) => t[T](Closed(s))

  private val big = Lang.big
  private def num(n: Int): Final[BigInt] = [T[_]] => (s: Sym[T]) => s.lit(BigInt(n), Value.Num(n), big)
  private def lit[A](a: A, v: Value, ty: Ty): Stated[A] = Stated([T[_]] => (s: Sym[T]) => s.lit(a, v, ty))
  private val nums: List[Int] = List(1, 3)
  /** `p` is `n ≤ 1`; the others constants. */
  private val values: Map[String, Stated[?]] = Map(
    "p" -> Stated([T[_]] => (s: Sym[T]) => s.lam(Bound[BigInt]("n", big))(n => s.le(n, num(1)[T](s)))),
    "k" -> Stated(num(2)),
    "xs" -> lit(nums.map(BigInt(_)), Value.Many(nums.map(Value.Num(_))), Ty.ListOf(big)),
    "o" -> lit(Option(BigInt(1)), Value.Maybe(Some(Value.Num(1))), Ty.OptionOf(big)),
    "slot" -> lit(Booking("Oak", 1, 3), Value.Data(CtorName("mk"), List(Value.Str("Oak"), Value.Num(1),
      Value.Num(3))), Booking.ty),
    "s" -> lit(Set(BigInt(0), BigInt(2)), Value.Many(List(Value.Num(0), Value.Num(2))), Ty.SetOf(big)),
    "m" -> lit(Map(BigInt(1) -> BigInt(2)), Value.Pairs(List(Value.Num(1) -> Value.Num(2))), Ty.MapOf(big, big)),
    "ev" -> lit[Event](Event.Booked(2), Value.Data(CtorName("Booked"), List(Value.Num(2))), MoreTerms.eventTy),
    "outcome" -> lit[Either[String, BigInt]](Right(BigInt(1)), Value.Inject(Side.Value, Value.Num(1)),
      MoreTerms.outcomeTy))
