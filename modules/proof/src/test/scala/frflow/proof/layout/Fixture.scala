package frflow.proof.layout

import frflow.core.{Booking, Lang}
import frflow.core.expr.Binder
import frflow.core.name.{DefName, SourceText, VarId}
import frflow.core.Nodes.*
import frflow.core.spec.{Node, Written}
import frflow.core.term.{Bound, Selector}
import frflow.core.term.language.{Final, Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}

/** What the test theories of proven code are written with: variables, terms, and what
  * always holds of a booking (its rule, the claim, and the assumption of it on what comes from outside).
  */
object Fixture:
  def at(i: Int, hint: String, ty: Ty): Binder = Binder(VarId.level(i), hint, ty)
  def term[A](f: [T[_]] => Sym[T] => T[A]): Stated[A] = Stated([T[_]] => (s: Sym[T]) => f(s))
  def v[A](x: Binder): Stated[A] = term([T[_]] => (s: Sym[T]) => s.free[A](x))
  def fn(in: Ty, out: Ty): Ty = Ty.FnOf(List(in), out)
  /** A booking's room (core's fixtures read its times only). */
  val room: Selector[Booking, String] = Selector("room", 0, Booking.name, Ty.Str, _.room, (b, r) => b.copy(room = r))

  /** `(Booking.mk room start end)`. */
  def booking[T[_]](s: Sym[T], room: T[String], start: T[BigInt], end: T[BigInt]): T[Booking] =
    s.app(s.app(s.app(s.construct(Booking.make), room), start), end)

  private val b = at(0, "b", Booking.ty)
  /** `b.start < b.end`, a define named as the claim of it. */
  val endsRule: Define = rule("endsAfterStart")
  /** The same rule, a define named as another statement of it (an assumption of always has its rule too). */
  def rule(name: String): Define = Define(DefName(name), Written.lambda(List(b), [T[_]] => (s: Sym[T]) =>
    s.lt(s.field(s.free[Booking](b), Booking.start), s.field(s.free[Booking](b), Booking.end)),
    SourceText(name)), DefineForm.Function)

  private val ends: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always(Bound[Booking]("b", Booking.ty))(x => l.s.lt(l.s.field(x, Booking.start), l.s.field(x, Booking.end))))
  val endsAfterStart: Node = claim("endsAfterStart")(ends)
  /** What the outside sends meets the same rule (owner §21). */
  def fromOutside(id: String): Node = assumption(id)(ends)
