package frflow.api.node

import frflow.core.name.NodeId
import frflow.decision.review.{Mechanical, Standing}

/** Where the developer stands on a node: its version as shown (a decision sent with it is refused once it moved:
  * `Refusal.MovedSinceSeen`), its state and causes, its decisions (of those that count), what it waits for, why it is
  * not a mechanical decision (none: `confirm` takes it), and how deciding it relates to the nodes around it.
  */
final case class ReviewView(version: String, standing: Standing, decisions: Decisions, waitsFor: Option[NodeId],
    notMechanical: Option[Mechanical.Not], moves: Movement)
