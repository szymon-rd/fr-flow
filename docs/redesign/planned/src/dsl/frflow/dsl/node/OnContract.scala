package frflow.dsl.node

import frflow.core.example.{CallExample, RunExample}
import frflow.core.spec.{Reliance, Statement}
import frflow.dsl.build.Deferred

/** A contract's case: a promise that can also leave its word open to the nodes above (`leftOpenAbove`). */
trait OnContract[S <: Statement] extends OnPromise[S]:
  def leftOpen(s: S): S

object OnContract:
  given OnContract[Statement.Contract] with
    type Example = CallExample
    def leftOpen(s: Statement.Contract): Statement.Contract = s.copy(reliance = Reliance.LeftOpen)
    def withExamples(s: Statement.Contract, more: List[CallExample]): Statement.Contract =
      s.copy(promise = s.promise.withExamples(more))
    def examples[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[CallExample]] =
      Examples.calls(head, givens, cases)

  given OnContract[Statement.FlowContract] with
    type Example = RunExample
    def leftOpen(s: Statement.FlowContract): Statement.FlowContract = s.copy(reliance = Reliance.LeftOpen)
    def withExamples(s: Statement.FlowContract, more: List[RunExample]): Statement.FlowContract =
      s.copy(promise = s.promise.withExamples(more))
    def examples[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[RunExample]] =
      Examples.runs(head, givens, cases)
