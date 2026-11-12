package frflow.eval.prices

import frflow.core.analysis.Validate
import scala.annotation.experimental

/** A structure with no class, known by an assumption: the model that holds it is valid (Lean: not yet). */
@experimental class TrustedPricesSuite extends munit.FunSuite:
  test("a basket over a price list that is only assumed of is a valid model") {
    val elaborated = TrustedPricesModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }
