package frflow.testing

import frflow.core.code.{Impl, Values}
import frflow.core.Elaborated
import frflow.core.expr.Value
import frflow.eval.run.{Broken, CallCheck, Echo}
import frflow.eval.Semantics

/** A generated case judged as the running service used to judge each call, before production. */
class PropertyTestsSuite extends munit.FunSuite:
  private val loses: String => String = s => if s.length > 3 then s.take(3) else s
  private val elaborated = Elaborated(Echo.theory(loses), Map.empty, Nil)
  private val semantics = Semantics(elaborated)
  private val tests = PropertyTests(semantics, elaborated.theory)

  test("the first generated case the code breaks its post on is found, with what it broke") {
    val check = CallCheck.of(semantics, elaborated.theory, Echo.claim).getOrElse(fail("Echo is a contract"))
    val cases = List("ab", "abc", "abcd", "abcde").map(s => Case(List(Value.Str(s)), Values.none))
    assertEquals(tests.firstFailing(check, Impl(1, _ => loses), cases), Some(cases(2) -> Broken.Post))
  }
