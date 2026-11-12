package frflow.eval

import frflow.core.analysis.Validate
import scala.annotation.experimental

/** The payment stream (`examples/payments`): its model, each service a Definition given a class FrFlow reads, is
  * valid.
  */
@experimental class PaymentsSuite extends munit.FunSuite:
  private val elaborated = payments.payments.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the stream's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }
