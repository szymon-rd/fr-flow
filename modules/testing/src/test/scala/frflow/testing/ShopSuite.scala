package frflow.testing

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import shop.ShopExamples
import scala.annotation.experimental

/** The shop (`examples/shop`): its model, each store and service a Definition given a class FrFlow reads, is valid,
  * and its examples hold of the code read from the classes.
  */
@experimental class ShopSuite extends munit.FunSuite:
  private val elaborated = shop.shop.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the shop's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("its examples hold of its code: the forgetful checkout's unit left held among them") {
    val examples = ShopExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 5)
  }
