package frflow.proof.lean

import frflow.core.{Booking, Lang}
import frflow.core.expr.{Side, Value}
import frflow.core.ty.Ty
import frflow.proof.layout.Mini
import frflow.proof.lean.lower.{LowerValue, Naming}
import frflow.proof.lean.print.Print

/** The lowering of what is not a term: constants of every kind of value (maps and sets among them). */
class LowerSuite extends munit.FunSuite:
  private val env = frflow.proof.layout.Lowering(Mini.resolved, frflow.proof.terms.TermTable.of(Mini.resolved)).env
  private def lowered(v: Value, t: Ty): String = Print.expr(LowerValue(env)(v, t).runA(Naming.over(Set.empty,
    Set.empty)).value)
  private val (a, b) = (Value.Str("a"), Value.Str("b"))

  test("constants: numbers, strings, lists, options, records, eithers, tuples") {
    assertEquals(lowered(Value.Num(-2), Lang.big), "(-2)")
    assertEquals(lowered(Value.Many(List(a, b)), Ty.ListOf(Ty.Str)), "[\"a\", \"b\"]")
    assertEquals(lowered(Value.Maybe(Some(Value.Num(1))), Ty.OptionOf(Lang.big)), "(some 1)")
    assertEquals(lowered(Mini.booking, Booking.ty), "(Booking.mk \"\" 0 1)")
    assertEquals(lowered(Value.Tuple(List(a, Value.Bool(true))), Ty.TupleOf(List(Ty.Str, Ty.Bool))), "(\"a\", True)")
    assertEquals(lowered(Value.Inject(Side.Error, a), Ty.EitherOf(Ty.Str, Lang.big)), "(Except.error \"a\")")
  }

  test("a map is a function to options, a set a predicate, each over a helper no value names") {
    assertEquals(lowered(Value.Pairs(List(a -> Value.Num(1), b -> Value.Num(2))), Ty.MapOf(Ty.Str, Lang.big)),
      "(fun k => if k = \"a\" then (some 1) else if k = \"b\" then (some 2) else none)")
    assertEquals(lowered(Value.Many(List(Value.Num(1), Value.Num(2))), Ty.SetOf(Lang.big)), "(fun x => x = 1 ∨ x = 2)")
    assertEquals(lowered(Value.Many(Nil), Ty.SetOf(Lang.big)), "(fun x => False)")
  }
