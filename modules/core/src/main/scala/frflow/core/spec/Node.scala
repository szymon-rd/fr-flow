package frflow.core.spec

import frflow.core.name.NodeId

/** One decided statement: its id, its sentence, and what it says. Why it holds is the reason of its signed decision
  * (the ledger's), not part of the node. Its edges, code, position and checks are kept apart.
  */
final case class Node(id: NodeId, says: String, statement: Statement)
