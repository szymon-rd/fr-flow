package frflow.core.analysis

import cats.data.NonEmptyList
import frflow.core.{Booking, Kb, Lang}
import frflow.core.Nodes.claim
import frflow.core.expr.{Expr, Exprs, Pattern, Side}
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.Bound
import frflow.core.term.interpret.{Guarded, ToExpr}
import frflow.core.ty.{Ctor, DataType, Field, Ty}

/** `always[T]`'s guard reaches every `T` a value holds, wherever `Scope.holds` finds one (owner §16): an option's
  * value, an `Either`'s side, a pair's component and an enum case's field, as a list's element and a record's field.
  */
class GuardsSuite extends munit.FunSuite:
  private val change = DataType.Sum(TypeName("Change"), "Change", NonEmptyList.of(
    Ctor(CtorName("book"), List(Field("b", Booking.ty))), Ctor(CtorName("clear"), Nil)))
  private val ends = claim("endsAfterStart")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.always[Booking](Bound("b", Booking.ty))(b => l.s.eq(b, b))))
  private val theory = Kb.of(ends).declaring(_.copy(types = List(Booking.data, change))).theory

  /** The patterns and projections of the hypothesis a variable of `ty` comes with. */
  private def guarded(ty: Ty): List[Expr] =
    Exprs.all(ToExpr.of(Guarded.of(Lang.formula([T[_]] => (l: Lang[T]) => l.forall[Any]("x", ty)(_ => l.truth)),
      Guards.of(theory)))).collect { case e @ (Expr.Match(_, _, _) | Expr.Field(_, _, _, _)) => e }

  private def patterns(es: List[Expr]): List[List[Pattern]] = es.collect { case Expr.Match(_, as, _) =>
    as.map(_.pattern) }

  test("each shape holding a booking is guarded; one holding none is not") {
    val shapes = List(Ty.OptionOf(Booking.ty), Ty.EitherOf(Ty.Str, Booking.ty), Ty.TupleOf(List(Ty.Str, Booking.ty)),
      Ty.Data(change.typeName), Ty.ListOf(Ty.OptionOf(Booking.ty)))
    assert(shapes.forall(Guards.applies(theory, Booking.ty, _)))
    assert(!List(Ty.Str, Ty.OptionOf(Ty.Str), Ty.TupleOf(List(Ty.Str, Ty.Str))).exists(Guards.applies(theory,
      Booking.ty, _)))
  }

  test("an option's value and an Either's side, by a match") {
    assertEquals(patterns(guarded(Ty.OptionOf(Booking.ty))).map(_.map(_.productPrefix)), List(List("NoneP", "SomeP")))
    assertEquals(patterns(guarded(Ty.EitherOf(Ty.Str, Booking.ty))).map(_.collect { case Pattern.Outcome(s, _) => s }),
      List(List(Side.Error, Side.Value)))
  }

  test("a pair's component, by its projection; an enum case's field, by a match on the enum") {
    assertEquals(guarded(Ty.TupleOf(List(Ty.Str, Booking.ty))).collect { case Expr.Field(_, d, i, t) => (d, i, t) },
      List.fill(2)((TypeName("Prod"), 1, Booking.ty)))
    assertEquals(patterns(guarded(Ty.Data(change.typeName))).map(_.collect { case Pattern.Ctor(_, c, fs) =>
      c.value -> fs.size }), List(List("book" -> 1, "clear" -> 0)))
  }
