package frflow.proof.obligation

import frflow.core.name.NodeId

/** Everything Lean is asked of one node: what must hold, and what is tried, each in today's order. */
final case class NodeObligations(node: NodeId, required: List[Obligation], tried: List[Obligation])
