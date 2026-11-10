package frflow.eval

import frflow.core.analysis.Validate
import frflow.testing.{Agreement, Settings}
import frflow.testing.Agreement.Outcome
import frflow.testing.report.Seed
import scala.annotation.experimental

/** The spike's desk: its service method changes the port it is given, its model is a function of the port's state,
  * and the two agree: the Scala run on a table made from the rows gives what the evaluator gives of the term read.
  */
@experimental class DeskSuite extends munit.FunSuite:
  import Desk.{Booking, Table}

  private val elaborated = DeskModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the desk's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("the table as production uses it is changed by its methods; the model's Scala gives the rows it leaves") {
    val table = Table(List(Booking("Oak", 9, 10)))
    table.add(Booking("Oak", 10, 11))
    assertEquals(table.rows, List(Booking("Oak", 9, 10), Booking("Oak", 10, 11)))
    assertEquals(Desk.book(List(Booking("Oak", 9, 10)), Booking("Oak", 9, 11)), (false, List(Booking("Oak", 9, 10))))
  }

  test("its Scala, run on a table made from the rows, agrees with the term read from it on generated cases") {
    assertEquals(Agreement(elaborated).of(Desk.book, Settings(300, Seed(1))).outcome, Outcome.Agree(300))
  }
