package frflow.eval.prices

import frflow.core.analysis.Validate
import frflow.core.analysis.resolution.Constrained
import frflow.core.name.NodeId
import scala.annotation.experimental

/** A structure reached through the one that holds its holder: a claim on a counter says of the price list its
  * basket holds, by the words of each holding in turn.
  */
@experimental class CounterSuite extends munit.FunSuite:
  private lazy val elaborated =
    CounterModel.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("a model whose claims reach a structure two constructors down is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("a structure read beside the holder of its holder is what that one holds through it") {
    val words = Constrained.of(elaborated.theory, NodeId("ringingKeepsThePriceList")).map(_.value).toSet
    assertEquals(words, Set("counter_ring", "counter_holds_basket", "basket_holds_pricing", "pricing_price"))
  }
