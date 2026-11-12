package frflow.proof.reading

import frflow.core.name.NodeId

/** An authored proof file (`rocq/Proofs/<Model>/<node>.v`) as read: whose it is, and its text. */
final case class ProofFile(node: NodeId, source: String)
