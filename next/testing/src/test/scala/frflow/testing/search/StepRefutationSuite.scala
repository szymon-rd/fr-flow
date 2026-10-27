package frflow.testing.search

import frflow.*
import frflow.core.analysis.{Resolve, Validate}
import frflow.core.expr.{Expr, Lambda, Value}
import frflow.core.name.NodeId
import frflow.core.spec.CallForm
import frflow.eval.Semantics
import frflow.eval.run.Echo
import frflow.testing.Case

/** The answer a part's claim fixes (`guard implies op(inputs) === e`), which a refuted step is searched with: the
  * Definition answering `e` everywhere, a case the claim above fails on.
  */
class StepRefutationSuite extends munit.FunSuite:
  private val post: Lambda = Echo.theory((s: String) => s).node(Echo.claim).flatMap(_.statement.call).collect {
    case CallForm.Call(_, p) => p.value
  }.getOrElse(fail("echo's claim reads as a call"))

  test("of `echo(x) === x`, the answer is `x`; of a claim not fixing echo's result, none") {
    assertEquals(StepRefutation.answerOf(post, Echo.op), post.params.headOption.map(Expr.Var(_)))
    assertEquals(StepRefutation.answerOf(post.copy(body = Expr.Var(post.params.head)), Echo.op), None)
  }

  private val d = Definition[BigInt => BigInt]("a number the service gives for another")
  private val nonNegative = Node.claim("The service never gives a negative number.")(
    forall((n: Term[BigInt]) => d(n) >= 0))
  private val sameAbove = Node.claim("Above zero, the service gives the number itself.")(
    forall((n: Term[BigInt]) => (n > 0) implies (d(n) === n))).refines(nonNegative)

  test("a step whose part fixes the answer only above zero is refuted at a case below it, with that answer") {
    val e = FrModel("Steps")(nonNegative, sameAbove).implementTested(d)(_ => n => n.abs).elaborated
      .fold(es => fail(es.toString), identity)
    val r = Resolve(Validate(e).fold(ps => fail(ps.toString), identity))
    val cases = List(1, 0, -1, -2).map(n => Case(List(Value.Num(n)), Nil))
    val found = StepRefutation.candidate(Semantics(e), r, NodeId("nonNegative"), cases)
    assertEquals(found.map(_.inputs.map(_._2)), Some(List(Value.Num(-1))))
    assert(found.exists(_.answer match { case Expr.Var(_) => true; case _ => false }), found)
    assertEquals(StepRefutation.candidate(Semantics(e), r, NodeId("nonNegative"), cases.take(2)), None)
  }
