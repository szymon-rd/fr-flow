package frflow.dsl.node

import frflow.core.example.CallExample
import frflow.core.spec.Statement
import frflow.dsl.build.Deferred

/** What `examples` needs of a node with a promise: its examples' shape. A contract on a function and an assumption
  * about an operation take calls, a contract on a flow takes runs; `examples` is written once over this.
  */
trait OnPromise[S <: Statement]:
  type Example
  def withExamples(s: S, more: List[Example]): S
  def examples[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[Example]]

object OnPromise:
  /** Every contract's instance (in `OnContract`'s companion) is a promise's. */
  given [S <: Statement](using c: OnContract[S]): OnPromise[S] = c

  given OnPromise[Statement.AssumedCall] with
    type Example = CallExample
    def withExamples(s: Statement.AssumedCall, more: List[CallExample]): Statement.AssumedCall =
      s.copy(promise = s.promise.withExamples(more))
    def examples[F](head: Head, givens: List[Binding], cases: List[Case[F]]): Deferred[List[CallExample]] =
      Examples.calls(head, givens, cases)
