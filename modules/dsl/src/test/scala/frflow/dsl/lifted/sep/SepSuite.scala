package frflow.dsl.lifted.sep

import frflow.core.expr.{Expr, Lambda}
import frflow.core.ty.Ty
import scala.annotation.experimental

/** The spike: direct-style Scala over a port, compiled under Scala's capture and separation checking, is read into
  * a function of the port's state that gives its result with the state after it; and the checking the reading
  * rests on still refuses a port aliased or changed through a reference that only reads.
  */
@experimental class SepSuite extends munit.FunSuite:
  import SepA.{Slot, Table}

  private def lambda(d: frflow.dsl.vocab.Definition[?]): Lambda =
    d.onTheSpot.fold(fail("no meaning"))(_.lambda.run.fold(es => fail(es.toChain.toList.mkString("; ")), _._2.value))

  test("a service method reads as a function of the port's state: its result, with the state after it") {
    val read = lambda(SepB.book.model)
    val rows = Ty.ListOf(Ty.Data(frflow.core.name.TypeName("Slot")))
    assertEquals((read.params.map(p => p.hint -> p.ty), read.result),
      (List("table" -> rows, "request" -> Ty.Data(frflow.core.name.TypeName("Slot"))),
        Ty.TupleOf(List(Ty.Bool, rows))))
  }

  test("what follows a change reads the state the change left") {
    lambda(SepB.replace.model).body match
      case Expr.Let(cleared, Expr.ListOf(Nil, _), Expr.Let(added, Expr.Prim(_, List(Expr.Var(from), _), _), _)) =>
        assertEquals(from.id, cleared.id, s"$added is not made from $cleared")
      case other => fail(s"not two changes in sequence: $other")
  }

  test("the Scala as written changes the port; its model, run on a port made from the state, gives the state") {
    val table = Table(List(Slot("Oak", 9, 10)))
    assert(SepB.book.run(table, Slot("Oak", 10, 11)))
    assertEquals(table.rows, List(Slot("Oak", 9, 10), Slot("Oak", 10, 11)))
    assertEquals(SepB.book.model(List(Slot("Oak", 9, 10)), Slot("Oak", 9, 11)), (false, List(Slot("Oak", 9, 10))))
    assertEquals(SepB.replace.model(List(Slot("Oak", 9, 10)), Slot("Elm", 1, 2)), (true, List(Slot("Elm", 1, 2))))
  }

  test("a service method that is an ordinary def reads as the lambda written out does") {
    assertEquals(lambda(SepB.reserved.model).result, lambda(SepB.book.model).result)
    assertEquals(SepB.reserved.model(List(Slot("Oak", 9, 10)), Slot("Oak", 10, 11)),
      (true, List(Slot("Oak", 9, 10), Slot("Oak", 10, 11))))
    assertEquals(SepA.reserveBoth(Slot("Oak", 9, 10), Slot("Oak", 10, 11)).size, 2)
  }

  test("a change of a port inside a function given to an operation is not read") {
    assert(SepB.inLambda.exists(_.contains("lifted code cannot hold")), SepB.inLambda.mkString(" | "))
  }
