package frflow.proof.lean.laws

import cats.data.NonEmptyList
import frflow.core.{Lang, Booking}
import frflow.core.expr.{Terms, Tm}
import frflow.core.expr.Tm.*
import frflow.core.name.{CtorName, ModelName, SymbolName, TypeName}
import frflow.core.term.{Bound, Case, Constructor, Final, Program, Selector, Sym, When, World}
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import scala.util.Random

/** Random terms over the algebras core's `Terms` leaves out: a sum's eliminator, eithers, pairs, a program's runs and
  * failures between worlds and a model's part of one; their numbers and conditions are core's.
  */
final class MoreTerms(seed: Long):
  import MoreTerms.*
  private val r = Random(seed)
  private val inner = Terms(seed + 1)

  def formula: Final[Boolean] = Tm.closed(bool(3, 0))

  def bool(d: Int, k: Int): Tm[Boolean] = if d <= 0 then inner.bool(0, k) else r.nextInt(6) match
    case 0 => matched(d - 1, k)
    case 1 => either(d - 1, k)
    case 2 => Tm.eq(pairOf(d - 1, k), pairOf(d - 1, k))
    case 3 => runs(d - 1, k)
    case 4 => fails(d - 1, k)
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

  /** `∀ (before : World), match (run n before) with | (result, after) => …`, reading the store's part. */
  private def runs(d: Int, k: Int): Tm[Boolean] =
    val (n, post) = (inner.num(d, k), inner.bool(d, k + 1))
    [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) =>
      s.forall(Bound[World]("before", Ty.World))(w => s.runs(program(s, n(s, c), "run"), w,
        Bound[BigInt]("result", Lang.big), Bound[World]("after", Ty.World))((res, after) =>
        s.and(post(s, c.bind(res)),
          s.eq(s.part[BigInt](after, stored, Lang.big), s.part[BigInt](w, stored, Lang.big)))))

  private def fails(d: Int, k: Int): Tm[Boolean] =
    val (n, post) = (inner.num(d, k), inner.bool(d, k))
    [T[_]] => (s: Sym[T], c: frflow.core.expr.Scope[T]) =>
      s.forall(Bound[World]("before", Ty.World))(w => s.fails(program(s, n(s, c), "attempt"), w,
        Bound[String]("error", Ty.Str),
        Bound[World]("after", Ty.World))((_, _) => post(s, c)))

  /** `run`, a program that never fails; `attempt`, one that may (Lean's `Except String Int × World`). */
  private def program[T[_]](s: Sym[T], n: T[BigInt], name: String): T[Program[BigInt]] =
    s.app(s.param[BigInt => Program[BigInt]](SymbolName(name), runTy), n)

object MoreTerms:
  val eventName: TypeName = TypeName("Event")
  val eventTy: Ty = Ty.Data(eventName)
  val event: DataType = DataType.Sum(eventName, "Event", NonEmptyList.of(
    Ctor(CtorName("Booked"), List(Field("at", Lang.big))), Ctor(CtorName("Cleared"), Nil)))
  val outcomeTy: Ty = Ty.EitherOf(Ty.Str, Lang.big)
  val runTy: Ty = Ty.FnOf(List(Lang.big), Ty.FlowOf(Lang.big, None))
  val stored: ModelName = ModelName("stored")
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
