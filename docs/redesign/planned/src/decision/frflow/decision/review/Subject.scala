package frflow.decision.review

import frflow.core.name.NodeId
import frflow.decision.content.{CodeNow, Content}

/** A node as decisions see it: the ledger's whole view of the knowledge base. */
final case class Subject(id: NodeId, content: Content, place: Place, code: Option[CodeNow], proof: ProofStanding)
