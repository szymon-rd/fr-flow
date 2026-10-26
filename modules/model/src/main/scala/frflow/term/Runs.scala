package frflow
package term

import frflow.types.Shape

/** A flow's run in a statement: `book(request).answer(before)` and `stored.in(book(request).after(before))`, the run
  * of `book(request)` from the world `before`. A claim on the flow quantifies over its inputs and the world before:
  * `forall((request: Term[Booking], before: Term[World]) => …)`. Found on any flow's term (`Term` extends it).
  */
private[frflow] trait Runs:
  extension [R](run: Term[Flow[R]])
    /** What the run from `before` answers. */
    def answer(before: Term[World]): Term[R] = Term(Tree.Proj(Runs.from(run, before), 1, 2), Runs.resultOf(run))
    /** The world after the run from `before`. */
    def after(before: Term[World]): Term[World] = Term(Tree.Proj(Runs.from(run, before), 2, 2), summon[LeanType[World]])

private object Runs:
  def from(run: Term[?], before: Term[World]): Tree = Tree.RunOn(run.termTree, before.termTree)
  def resultOf[R](run: Term[Flow[R]]): LeanType[R] = run.termType.shape match
    case Shape.FlowOf(r) => r.asInstanceOf[LeanType[R]]
    case _               => LeanType.unknown[R]
