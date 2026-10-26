package frflow.decision.ledger

import frflow.core.name.NodeId

/** Ids a ledger may hold that FrFlow no longer decides: `IDEA` (`IDEA.md`, retired). Read and written back unchanged,
  * never a subject, never listed as gone.
  */
object Retired:
  val ids: Set[NodeId] = Set(NodeId("IDEA"))
