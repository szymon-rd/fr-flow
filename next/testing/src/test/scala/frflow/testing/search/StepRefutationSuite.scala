package frflow.testing.search

import frflow.core.expr.{Expr, Lambda}
import frflow.core.spec.CallForm
import frflow.eval.run.Echo

/** The answer a part's claim fixes (`guard implies op(inputs) === e`), which a refuted step is searched with. */
class StepRefutationSuite extends munit.FunSuite:
  private val post: Lambda = Echo.theory((s: String) => s).node(Echo.claim).flatMap(_.statement.call).collect {
    case CallForm.Call(_, p) => p.value
  }.getOrElse(fail("echo's claim reads as a call"))

  test("of `echo(x) === x`, the answer is `x`; of a claim not fixing echo's result, none") {
    assertEquals(StepRefutation.answerOf(post, Echo.op), post.params.headOption.map(Expr.Var(_)))
    assertEquals(StepRefutation.answerOf(post.copy(body = Expr.Var(post.params.head)), Echo.op), None)
  }
