package frflow.proof.reading

import frflow.core.name.NodeId

/** An authored proof file (`lean/Proofs/<KB>/<Node>.lean`) as read: whose it is, and its text. */
final case class ProofFile(node: NodeId, source: String)
