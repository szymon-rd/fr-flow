package frflow.project.program

import frflow.core.name.NodeId
import frflow.decision.ledger.Decision

/** The decisions a `decide` recorded, in the order taken. */
final case class Decided(recorded: List[(NodeId, Decision)])
