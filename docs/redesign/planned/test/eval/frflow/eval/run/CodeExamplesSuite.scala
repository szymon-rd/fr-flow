package frflow.eval.run

import frflow.core.code.Impl
import frflow.core.Elaborated
import frflow.core.example.{CallExample, Verdict}
import frflow.core.expr.Value
import frflow.eval.Denote

/** An operation's code run on its examples (today's `checkExamples` on code). */
class CodeExamplesSuite extends munit.FunSuite:
  private val wrong: String => String = _ => "wrong"
  private val theory = Echo.theory(wrong)
  private val denote = Denote(Elaborated(theory, Map.empty, Nil))

  test("an example the code returns something else for gives `Returned` with what it returned") {
    val check = CallCheck.of(denote, theory, Echo.contract).getOrElse(fail("Echo is a contract"))
    val examples = List(CallExample("echoes", Nil, List(Value.Str("hi")), Value.Str("hi"), Verdict.Expect))
    assertEquals(CodeExamples(denote, Givens.of(denote, theory), check, Impl(1, () => wrong)).of(examples),
      List(Agreement.Returned(Value.Str("wrong"))))
  }
