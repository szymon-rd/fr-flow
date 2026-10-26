package frflow.api.node

import frflow.core.name.NodeId
import frflow.decision.ledger.Decision
import frflow.decision.review.{Mechanical, Standing}

/** Where the developer stands on a node: its state and causes, the decision it is bound to, what it waits for, and
  * why it is not a mechanical decision (none: `confirm` takes it).
  */
final case class ReviewView(standing: Standing, decision: Option[Decision], waitsFor: Option[NodeId],
    notMechanical: Option[Mechanical.Not])
