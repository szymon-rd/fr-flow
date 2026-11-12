package frflow.eval

import frflow.core.expr.{Side, Value}
import frflow.core.name.CtorName
import frflow.core.ty.{NumKind, Ty}

/** Constants as Scala holds them (`Literals`) and back (`Reflect`): the law `Reflect(Literals(v, t), t) == v` on a
  * value of every type a constant takes, maps and sets among them; and each as Scala's own value.
  */
class LiteralsSuite extends munit.FunSuite:
  private val e = Trouble.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val (literals, reflect) = (Literals(e), Reflect(e))
  private val big = Ty.Num(NumKind.Big)
  private def n(i: Int): Value = Value.Num(i)
  private val trouble = Ty.Data(frflow.core.name.TypeName("Trouble"))

  private val constants: List[(Value, Ty)] = List(
    Value.Bool(true) -> Ty.Bool, Value.Str("Oak") -> Ty.Str, n(-3) -> big, Value.Unit -> Ty.Unit,
    Value.Many(List(n(1), n(2))) -> Ty.ListOf(big), Value.Maybe(Some(n(1))) -> Ty.OptionOf(big),
    Value.Maybe(None) -> Ty.OptionOf(big), Value.Tuple(List(n(1), Value.Str("a"))) -> Ty.TupleOf(List(big, Ty.Str)),
    Value.Inject(Side.Error, Value.Str("no")) -> Ty.EitherOf(Ty.Str, big),
    Value.Inject(Side.Value, n(4)) -> Ty.EitherOf(Ty.Str, big),
    Value.Pairs(List(n(1) -> n(2), n(3) -> n(4))) -> Ty.MapOf(big, big),
    Value.Many(List(n(0), n(2))) -> Ty.SetOf(big),
    Value.Data(CtorName("TooBig"), List(n(3))) -> trouble, Value.Data(CtorName("Down"), Nil) -> trouble)

  test("a number is read as a Scala Int or Long only where it fits: one that does not is never wrapped around") {
    assertEquals(literals(Value.Num(BigInt(Int.MaxValue)), Ty.Num(NumKind.Int32)).unwrap, Int.MaxValue)
    assertEquals(literals(Value.Num(BigInt(1) << 40), Ty.Num(NumKind.Int64)).unwrap, 1L << 40)
    List(Value.Num(BigInt(1) << 40) -> NumKind.Int32, Value.Num(BigInt(1) << 70) -> NumKind.Int64).foreach((v, k) =>
      intercept[IllegalStateException](literals(v, Ty.Num(k))))
    assertEquals(NumKind.Int32.nearest(BigInt(1) << 40), BigInt(Int.MaxValue))
  }

  test("a constant made Scala's and read back is the constant") {
    constants.foreach((v, t) => assertEquals(reflect(literals(v, t), t), v, t))
  }

  test("maps, sets and data are Scala's own") {
    assertEquals(literals(Value.Pairs(List(n(1) -> n(2))), Ty.MapOf(big, big)).unwrap, Map(BigInt(1) -> BigInt(2)))
    assertEquals(literals(Value.Many(List(n(0), n(2))), Ty.SetOf(big)).unwrap, Set(BigInt(0), BigInt(2)))
    assertEquals(literals(Value.Data(CtorName("TooBig"), List(n(3))), trouble).unwrap, Trouble.TooBig(3))
  }
