package frflow.proof.lean

import frflow.core.{Booking, Lang}
import frflow.core.expr.{Side, Value}
import frflow.core.name.ModelName
import frflow.core.ty.Ty
import frflow.proof.layout.{Mini, Programs, ProgramsProject}
import frflow.proof.lean.lower.{LowerValue, Naming}
import frflow.proof.lean.print.Print

/** The lowering of what is not a term: a program's steps (raise, catch, collect, accumulate: `Programs.careful`), and
  * constants of every kind of value (maps, sets, worlds among them).
  */
class LowerSuite extends munit.FunSuite:
  private def module(name: String): String =
    ProgramsProject.modules.find(_.name.dotted == s"FrFlowGen.Test.$name").fold(fail(s"no module $name"))(Print.module)

  test("a program raising, handling, collecting and accumulating: tryCatchThe, throwThe, mapM, foldlM") {
    val expected = """@[frflow_defs] def careful {m : Type → Type} [Monad m] [MonadExceptOf String m] : Int → m Int :=
      |  fun (n : Int) => do
      |    let r ← tryCatchThe String (do
      |        throwThe String "no")
      |      (fun e => do
      |        pure n)
      |    let ys ← ([1, 2] : (List Int)).mapM fun y => do
      |      pure (y + r)
      |    ys.foldlM (init := (0 : Int)) fun acc z => do
      |      pure (acc + z)""".stripMargin
    assert(module("Domain.Def_careful").contains(expected), module("Domain.Def_careful"))
  }

  test("a program's monad is named apart from every symbol") {
    assert(module("Domain.Def_both").contains("def both {m : Type → Type} [Monad m] : Int → m (Int × Int)"))
    assert(Programs.resolved.theory.vocabulary.symbols.forall(_.name.value != "m"))
  }

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

  test("a world: each model's state, in its structure") {
    assertEquals(lowered(Value.World(List(ModelName("stored") -> Value.Many(List(Mini.booking))), Nil), Ty.World),
      "(World.mk [(Booking.mk \"\" 0 1)])")
  }
