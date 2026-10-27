package frflow.project.report

import frflow.core.name.{NodeId, RelPath}
import frflow.decision.ledger.{Decision, Uncounted}
import frflow.decision.review.{ReviewState, Standing}
import frflow.project.pipeline.Analysis

/** `review`: every node in the order decisions are taken, as it stands; the decided nodes no longer in the model;
  * the decisions in the ledger that do not count, each with why; and the `.lean` files under `lean/Proofs/` that are
  * no node's proof (no check runs while one is there).
  */
final case class Review(nodes: List[Reviewed], gone: List[NodeId], uncounted: List[(NodeId, Decision, Uncounted)],
    strays: List[RelPath])

object Review:
  def of(a: Analysis): Review =
    val r = a.reading
    Review(a.subjects.inOrder.map(s => Reviewed(s, r.standings.getOrElse(s.id, Standing(ReviewState.Proposed, Nil)),
      r.waitsFor(s), r.notMechanical.get(s.id).flatten)), r.gone, a.inputs.ledger.others, a.inputs.lean.strays)
