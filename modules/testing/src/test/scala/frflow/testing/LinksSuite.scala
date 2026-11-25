package frflow.testing

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics
import links.LinksExamples
import scala.annotation.experimental

/** The link shortener (`examples/links`): its model, the shortener a Definition given a class FrFlow reads, is
  * valid, and its examples hold of the code read from the class.
  */
@experimental class LinksSuite extends munit.FunSuite:
  private val elaborated = links.links.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the shortener's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("its examples hold of its code") {
    val examples = LinksExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 3)
  }
