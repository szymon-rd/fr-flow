package frflow.dsl.lifted.sep

import frflow.core.expr.{Expr, Lambda}
import frflow.core.ty.Ty
import scala.annotation.experimental

/** The spike: direct-style Scala over a port, compiled under Scala's capture and separation checking, is read into
  * a function of the port's state that gives its result with the state after it; and the checking the reading
  * rests on still refuses a port aliased or changed through a reference that only reads.
  */
@experimental class SepSuite extends munit.FunSuite:
  import SepA.Slot

  private def lambda(d: frflow.dsl.vocab.Definition[?]): Lambda =
    d.onTheSpot.fold(fail("no meaning"))(_.lambda.run.fold(es => fail(es.toChain.toList.mkString("; ")), _._2.value))

  test("a service method reads as a function of the port's state: its result, with the state after it") {
    val read = lambda(SepB.book)
    val rows = Ty.ListOf(Ty.Data(frflow.core.name.TypeName("Slot")))
    assertEquals((read.params.map(p => p.hint -> p.ty), read.result),
      (List("rows" -> rows, "request" -> Ty.Data(frflow.core.name.TypeName("Slot"))),
        Ty.TupleOf(List(Ty.Bool, rows))))
  }

  test("what follows a change reads the state the change left") {
    lambda(SepB.replace).body match
      case Expr.Let(cleared, Expr.ListOf(Nil, _), Expr.Let(added, Expr.Prim(_, List(Expr.Var(from), _), _), _)) =>
        assertEquals(from.id, cleared.id, s"$added is not made from $cleared")
      case other => fail(s"not two changes in sequence: $other")
  }

  test("the model's Scala is the code run on a port made from the state: its result, with the state it leaves") {
    assertEquals(SepB.book(List(Slot("Oak", 9, 10)), Slot("Oak", 9, 11)), (false, List(Slot("Oak", 9, 10))))
    assertEquals(SepB.replace(List(Slot("Oak", 9, 10)), Slot("Elm", 1, 2)), (true, List(Slot("Elm", 1, 2))))
  }

  test("a service's method reads as the function written out does; among others it gives each step's states") {
    assertEquals(lambda(SepB.take), lambda(SepB.book).copy(params = lambda(SepB.take).params))
    assertEquals(SepB.take(Nil, Slot("Oak", 9, 10)), (true, List(Slot("Oak", 9, 10))))
    val among = lambda(SepB.takeAmongOthers)
    val rows = Ty.ListOf(Ty.Data(frflow.core.name.TypeName("Slot")))
    assertEquals(among.params.map(_.hint), List("rows", "between", "request"))
    assertEquals(among.result, Ty.TupleOf(List(Ty.Bool, Ty.ListOf(Ty.TupleOf(List(rows, rows))))))
  }

  test("a service method that is an ordinary def reads as the lambda written out does") {
    assertEquals(lambda(SepB.reserved).result, lambda(SepB.book).result)
    assertEquals(SepB.reserved(List(Slot("Oak", 9, 10)), Slot("Oak", 10, 11)),
      (true, List(Slot("Oak", 9, 10), Slot("Oak", 10, 11))))
    assertEquals(SepA.reserveBoth(Slot("Oak", 9, 10), Slot("Oak", 10, 11)).size, 2)
  }

  test("a service over two ports reads over a state with a field for each: a call changes its port's part") {
    val read = lambda(SepB.move)
    assertEquals(read.params.map(_.hint), List("rooms", "s"))
    assertEquals(read.result, Ty.TupleOf(List(Ty.Bool, Ty.Data(frflow.core.name.TypeName("Rooms")))))
    val oak = Slot("Oak", 9, 10)
    assertEquals(SepB.move(SepA.Rooms(List(oak), Nil), oak), (true, SepA.Rooms(Nil, List(oak))))
    assertEquals(SepB.move(SepA.Rooms(Nil, List(oak)), oak), (false, SepA.Rooms(Nil, List(oak))))
  }

  test("a service over several ports that names no state is refused") {
    assert(SepB.nameless.exists(_.contains("PortState")), SepB.nameless.mkString(" | "))
  }

  test("a change of a port inside a function given to an operation is not read") {
    assert(SepB.inLambda.exists(_.contains("lifted code cannot hold")), SepB.inLambda.mkString(" | "))
  }
