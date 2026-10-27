package frflow.api.view

import frflow.core.name.NodeId
import frflow.decision.ledger.Decision

/** The decisions a `decide` recorded, or a `preview` would, in the order taken. */
final case class Decided(recorded: List[(NodeId, Decision)])
