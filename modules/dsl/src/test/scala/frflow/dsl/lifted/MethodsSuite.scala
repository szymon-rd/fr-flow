package frflow.dsl.lifted

import frflow.core.expr.Lambda
import frflow.dsl.lifted.LiftSyntax.lifted
import frflow.dsl.shape.Defines.define
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition
import scala.compiletime.testing.typeCheckErrors

/** Ordinary methods called from lifted code, their bodies kept by the compiler (this module's tests compile with
  * `-Yretain-trees`): each call is the method's body read where it is called, its receiver the body's `this`.
  */
class MethodsSuite extends munit.FunSuite:
  private def lambda(d: Definition[?]): Lambda =
    d.onTheSpot.fold(fail(s"${d.name} has no meaning where it is written"))(_.lambda.run.fold(
      es => fail(es.toChain.toList.mkString("; ")), _._2.value))

  test("a case class's method: its body, the receiver its `this`") {
    val span = lifted { (b: Booking) => b.span }
    val written = define { (b: Term[Booking]) => b.end - b.start }
    assertEquals(lambda(span), lambda(written))
  }

  test("a method calling another of its class, and taking an input") {
    val lasts = lifted { (b: Booking, least: BigInt) => b.lasts(least) }
    val written = define { (b: Term[Booking], least: Term[BigInt]) => least <= b.end - b.start }
    assertEquals(lambda(lasts), lambda(written))
  }

  test("an object's functions, one calling another, each receiver its own body's `this`") {
    val free = lifted { (held: List[Booking], request: Booking) => Rules.free(held, request) }
    val written = define { (held: Term[List[Booking]], request: Term[Booking]) =>
      held.forall(b => b.room =!= request.room || b.end <= request.start || request.end <= b.start) }
    assertEquals(lambda(free), lambda(written))
    assert(free(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11)))
  }

  test("a method that calls itself is a recursion, which is not read") {
    val errors = typeCheckErrors("lifted { (n: BigInt) => Rules.countdown(n) }").map(_.message)
    assert(errors.exists(_.contains("calling itself: recursion is not read yet")), errors.mkString(" | "))
  }
