package frflow.eval

import frflow.core.expr.{Side, Value}
import frflow.core.name.CtorName
import frflow.core.term.World
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.model.Clock
import frflow.eval.flow.{Shelf, Trouble}

/** Constants as Scala holds them (`Literals`) and back (`Reflect`): the law `Reflect(Literals(v, t), t) == v` on a
  * value of every type a constant takes, maps, sets and worlds among them; and each as Scala's own value.
  */
class LiteralsSuite extends munit.FunSuite:
  private val e = Shelf.knowledge.elaborated.fold(es => throw AssertionError(es.iterator.mkString), identity)
  private val (literals, reflect) = (Literals(e), Reflect(e))
  private val big = Ty.Num(NumKind.Big)
  private def n(i: Int): Value = Value.Num(i)
  private val trouble = Ty.Data(frflow.core.name.TypeName("Trouble"))
  private val world = Value.World(List(Shelf.kept.name -> Value.Many(List(n(1))), Clock.clockModel.name -> n(0)),
    List(true, false))

  private val constants: List[(Value, Ty)] = List(
    Value.Bool(true) -> Ty.Bool, Value.Str("Oak") -> Ty.Str, n(-3) -> big, Value.Unit -> Ty.Unit,
    Value.Many(List(n(1), n(2))) -> Ty.ListOf(big), Value.Maybe(Some(n(1))) -> Ty.OptionOf(big),
    Value.Maybe(None) -> Ty.OptionOf(big), Value.Tuple(List(n(1), Value.Str("a"))) -> Ty.TupleOf(List(big, Ty.Str)),
    Value.Inject(Side.Error, Value.Str("no")) -> Ty.EitherOf(Ty.Str, big),
    Value.Inject(Side.Value, n(4)) -> Ty.EitherOf(Ty.Str, big),
    Value.Pairs(List(n(1) -> n(2), n(3) -> n(4))) -> Ty.MapOf(big, big),
    Value.Many(List(n(0), n(2))) -> Ty.SetOf(big),
    Value.Data(CtorName("TooBig"), List(n(3))) -> trouble, Value.Data(CtorName("Down"), Nil) -> trouble,
    world -> Ty.World)

  test("a constant made Scala's and read back is the constant") {
    constants.foreach((v, t) => assertEquals(reflect(literals(v, t), t), v, t))
  }

  test("maps, sets and data are Scala's own; a world holds each model's state and the faults") {
    assertEquals(literals(Value.Pairs(List(n(1) -> n(2))), Ty.MapOf(big, big)).unwrap, Map(BigInt(1) -> BigInt(2)))
    assertEquals(literals(Value.Many(List(n(0), n(2))), Ty.SetOf(big)).unwrap, Set(BigInt(0), BigInt(2)))
    assertEquals(literals(Value.Data(CtorName("TooBig"), List(n(3))), trouble).unwrap, Trouble.TooBig(3))
    val w = Fn.as[World](literals(world, Ty.World))
    assertEquals((w.state(Shelf.kept.name), w.state(Clock.clockModel.name), w.state(Faults.model)),
      (Some(List(BigInt(1))), Some(BigInt(0)), Some(List(true, false))))
  }

  test("faults: each call takes the next; none left, none fails") {
    val (after, first) = Faults.next(Map(Faults.model -> ScalaValue(List(true, false))))
    assertEquals((first, Faults.next(after)._2, Faults.next(Faults.next(after)._1)._2), (true, false, false))
  }
