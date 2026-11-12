package frflow.proof.lean.laws

import cats.data.NonEmptyList
import frflow.core.expr.{Terms, Tm}
import frflow.core.expr.Tm.*
import frflow.core.{Lang, Booking}
import frflow.core.name.{CtorName, SymbolName, TypeName}
import frflow.core.term.{Bound, Case, Constructor, Selector, When}
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import scala.util.Random

/** Random terms over the algebras core's `Terms` leaves out: a sum's eliminator, eithers and pairs; their numbers
  * and conditions are core's.
  */
final class MoreTerms(seed: Long):
  import MoreTerms.*
  private val r = Random(seed)
  private val inner = Terms(seed + 1)

  def formula: Final[Boolean] = Tm.closed(bool(3, 0))

  def bool(d: Int, k: Int): Tm[Boolean] = if d <= 0 then inner.bool(0, k) else r.nextInt(4) match
    case 0 => matched(d - 1, k)
    case 1 => either(d - 1, k)
    case 2 => Tm.eq(pairOf(d - 1, k), pairOf(d - 1, k))
    case _ => and(bool(d - 1, k), inner.bool(d - 1, k))

  /** `match e with | Event.Booked «at» => … | Event.Cleared => …`. */
  private def matched(d: Int, k: Int): Tm[Boolean] =
    val (e, booked, cleared) = (event(d, k), inner.bool(d, k + 1), inner.bool(d, k))
    [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) =>
      s.cases[Event, Boolean](e(s, c), List(
        When[T, Event, Event.Booked, Boolean](bookedCase, Bound("b", eventTy), b => booked(s, c.bind(s.field(b, at)))),
        When[T, Event, Event.Cleared.type, Boolean](clearedCase, Bound("c", eventTy), _ => cleared(s, c))), Ty.Bool)

  private def event(d: Int, k: Int): Tm[Event] =
    if r.nextBoolean() then param("ev", eventTy)
    else
      val n = inner.num(d, k)
      [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) => s.app(s.construct(booked), n(s, c))

  /** `match v with | Except.error e => … | Except.ok x => …` of an injection or a symbol. */
  private def either(d: Int, k: Int): Tm[Boolean] =
    val (n, onOk, onError) = (inner.num(d, k), inner.bool(d, k + 1), inner.bool(d, k))
    val side = r.nextInt(3)
    [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) =>
      val v: T[Either[String, BigInt]] = side match
        case 0 => s.left(Lang(s).str("full"), outcomeTy)
        case 1 => s.right(n(s, c), outcomeTy)
        case _ => s.param(SymbolName("outcome"), outcomeTy)
      s.foldEither(v, Bound[String]("e", Ty.Str), Bound[BigInt]("x", Lang.big))(_ => onError(s, c),
        x => onOk(s, c.bind(x)))

  private def pairOf(d: Int, k: Int): Tm[(BigInt, BigInt)] =
    val (a, b) = (inner.num(d, k), inner.num(d, k))
    [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) => s.pair(a(s, c), b(s, c))

object MoreTerms:
  val eventName: TypeName = TypeName("Event")
  val eventTy: Ty = Ty.Data(eventName)
  val event: DataType = DataType.Sum(eventName, "Event", NonEmptyList.of(
    Ctor(CtorName("Booked"), List(Field("at", Lang.big))), Ctor(CtorName("Cleared"), Nil)))
  val outcomeTy: Ty = Ty.EitherOf(Ty.Str, Lang.big)
  val booked: Constructor[BigInt => Event] = Constructor(eventName, CtorName("Booked"), Event.Booked(_))
  val at: Selector[Event.Booked, BigInt] = Selector("at", 0, eventName, Lang.big, _.at, (b, v) => b.copy(at = v))
  val bookedCase: Case[Event, Event.Booked] = Case(eventName, CtorName("Booked"), List("at" -> Lang.big), {
    case b: Event.Booked => Some(b)
    case _               => None
  })
  val clearedCase: Case[Event, Event.Cleared.type] = Case(eventName, CtorName("Cleared"), Nil, {
    case Event.Cleared => Some(Event.Cleared)
    case _             => None
  })
  /** Core's booking type, used beside the event. */
  val bookingData: DataType = Booking.data
