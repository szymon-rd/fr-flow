package frflow.project.report

import frflow.core.name.NodeId
import frflow.decision.ledger.{Decision, Uncounted}
import frflow.decision.review.{ReviewState, Standing}
import frflow.project.pipeline.Analysis

/** `review`: every node in the order decisions are taken, as it stands; the decided nodes no longer in the model;
  * and the decisions in the ledger that do not count, each with why.
  */
final case class Review(nodes: List[Reviewed], gone: List[NodeId], uncounted: List[(NodeId, Decision, Uncounted)])

object Review:
  def of(a: Analysis): Review =
    val r = a.reading
    Review(a.subjects.inOrder.map(s => Reviewed(s, r.standings.getOrElse(s.id, Standing(ReviewState.Proposed, Nil)),
      r.waitsFor(s), r.notMechanical.get(s.id).flatten)), r.gone, a.inputs.ledger.others)
