package frflow.eval

import frflow.core.analysis.Validate
import frflow.eval.run.{ExampleRun, OnCode}
import frflow.eval.term.Semantics

/** The calendar written in plain Scala (`Calendar`) is a model as any other: valid as written, and its examples,
  * facts in plain Scala among them, hold of its code.
  */
class CalendarSuite extends munit.FunSuite:
  private val elaborated = Calendar.model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)

  test("the calendar's model is valid") {
    assertEquals(Validate(elaborated).fold(_.toChain.toList.map(_.toString), _ => Nil), Nil)
  }

  test("its examples hold of its code, those written in plain Scala too") {
    val examples = CalendarExamples().elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity)
    val run = ExampleRun(Semantics(elaborated), elaborated.theory)
    assertEquals(examples.map(e => e.name -> run.of(e)).filterNot(_._2 == OnCode.Holds), Nil)
    assertEquals(examples.size, 3)
  }
