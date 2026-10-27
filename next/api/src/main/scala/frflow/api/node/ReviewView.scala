package frflow.api.node

import frflow.core.name.NodeId
import frflow.decision.ledger.Decision
import frflow.decision.review.{Mechanical, Standing}

/** Where the developer stands on a node: its version as shown (a decision sent with it is refused once it moved:
  * `Refusal.MovedSinceSeen`), its state and causes, the decision it is bound to (of those that count),
  * what it waits for, why it is not a mechanical decision (none: `confirm` takes it), what it rests on whose meaning
  * moved since it was decided (nearest first), and the decisions below it that accepting it acts on (parents first).
  */
final case class ReviewView(version: String, standing: Standing, decision: Option[Decision], waitsFor: Option[NodeId],
    notMechanical: Option[Mechanical.Not], movedAbove: List[NodeId], below: List[NodeId])
