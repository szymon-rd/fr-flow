package frflow.proof.layout.calls

import frflow.core.{Booking, Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.{Code, Impl, ScalaCode}
import frflow.core.name.{DefName, SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Body, Bound, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}
import frflow.proof.layout.Fixture.*

/** Proven defines handing plain Scala a value on the way through other code (owner §37), each a seeded bug: `ok` and
  * `twice` are plain Scala, and a booking must end after it starts.
  * - `spotCode` hands a booking with its times swapped to a define written on the spot, which hands it to `ok`;
  * - `definitionCode` hands it to `helping`, a Definition whose proven code `helper` hands it to `ok`;
  * - `eachCode` hands `ok` each booking `twice` gives, which nothing proven says ends after it starts.
  *
  * Each call's `made_` is open; `helper`'s own, of an input from outside, is proven.
  */
object Handed:
  private val b = at(0, "b", Booking.ty)
  private val check = Ty.FnOf(List(Booking.ty), Ty.Bool)
  private val listing = Ty.FnOf(List(Booking.ty), Ty.ListOf(Booking.ty))
  private def scala(name: String) = Code.Tested(ScalaCode(Impl(1, _ => ((_: Booking) => true)), SourceText(name),
    Nil), Nil)
  private def ok[T[_]](s: Sym[T], x: T[Booking]): T[Boolean] =
    s.app(s.param[Booking => Boolean](SymbolName("ok"), check), x)
  /** The booking `b`, its start and end swapped. */
  private def swapped[T[_]](s: Sym[T]): T[Booking] = booking(s, s.field(s.free[Booking](b), room),
    s.field(s.free[Booking](b), Booking.end), s.field(s.free[Booking](b), Booking.start))
  private def define(name: String)(body: [T[_]] => Sym[T] => T[Boolean]): Define =
    Define(DefName(name), Written.lambda(List(b), body, SourceText(name)), DefineForm.Function)

  private val helper = define("helper")([T[_]] => (s: Sym[T]) => ok(s, s.free[Booking](b)))
  /** `helper` as a define written on the spot calls it: by its body. */
  private val onTheSpot: Body[Booking => Boolean] = Body(DefName("helper"), check, [T[_]] => (s: Sym[T]) =>
    s.lam(Bound[Booking]("b", Booking.ty))(x => ok(s, x)))
  private val spotCode = define("spotCode")([T[_]] => (s: Sym[T]) => s.app(s.define(onTheSpot), swapped(s)))
  private val definitionCode = define("definitionCode")([T[_]] => (s: Sym[T]) =>
    s.app(s.param[Booking => Boolean](SymbolName("helping"), check), swapped(s)))
  private val eachCode = define("eachCode")([T[_]] => (s: Sym[T]) =>
    s.all(s.app(s.param[Booking => List[Booking]](SymbolName("twice"), listing), s.free[Booking](b)),
      Bound[Booking]("x", Booking.ty))(x => ok(s, x)))

  /** `∀ b, d b = d b` of each Definition: what mentions them. */
  private val mentioned = claim("mentioned")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[Booking]("b", Booking.ty)(x =>
      val same = List("ok", "spot", "byDefinition", "helping", "each").map(n =>
        l.s.eq(l.call(l.sym[Booking => Boolean](n, check), x), l.call(l.sym[Booking => Boolean](n, check), x)))
      val twice = l.call(l.sym[Booking => List[Booking]]("twice", listing), x)
      (same :+ l.s.eq(twice, twice)).reduceLeft(l.s.and))))

  val kb: Kb = Kb.of(endsAfterStart, fromOutside("fromOutside"), mentioned)
    .declaring(_.copy(types = List(Booking.data), defines = List(endsRule, rule("fromOutside"), helper, spotCode,
      definitionCode, eachCode)))
    .naming(definition("ok", check), definition("twice", listing), definition("spot", check),
      definition("byDefinition", check), definition("helping", check), definition("each", check))
    .coding(SymbolName("ok") -> scala("ok"), SymbolName("twice") -> scala("twice"),
      SymbolName("spot") -> Code.Proven(DefName("spotCode")),
      SymbolName("byDefinition") -> Code.Proven(DefName("definitionCode")),
      SymbolName("helping") -> Code.Proven(DefName("helper")), SymbolName("each") -> Code.Proven(DefName("eachCode")))
    .linking(assumes("endsAfterStart", "fromOutside"), assumes("mentioned", "fromOutside"))

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))
