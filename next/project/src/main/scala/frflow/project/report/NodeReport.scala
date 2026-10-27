package frflow.project.report

import frflow.core.name.NodeId
import frflow.decision.ledger.Decision
import frflow.project.pipeline.Analysis

/** `show`: one node as the review reads it, what earlier runs recorded of it while current, and the decision that
  * binds it (its reason is what the node is for).
  */
final case class NodeReport(reviewed: Reviewed, recent: Recent, binding: Option[Decision])

object NodeReport:
  /** None when the model has no such node. */
  def of(a: Analysis, id: NodeId): Option[NodeReport] =
    Review.of(a).nodes.find(_.subject.id == id).map(x =>
      NodeReport(x, Recent(a.current(id), a.tested(id)), a.inputs.ledger.counting.binding(id)))
