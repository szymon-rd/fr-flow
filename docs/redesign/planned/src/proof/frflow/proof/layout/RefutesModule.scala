package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.expr.{Expr, Value}
import frflow.core.name.NodeId
import frflow.proof.lean.ast.LeanModule

/** A step refuted (today's `Refutation.lean`): the theorem that the node's `complete` is false, given the answer its
  * one part fixes and the case `testing.StepRefutation` found, each value lowered by `LowerValue`.
  */
object RefutesModule:
  def of(r: Resolved, node: NodeId, answer: Expr, inputs: List[Value]): LeanModule = ???
