package frflow.proof.obligation

import frflow.core.name.NodeId

/** Everything Lean is asked of one node: what must hold, what is tried, and the evaluations, each in today's order. */
final case class NodeObligations(node: NodeId, required: List[Obligation], tried: List[Obligation],
    evaluated: List[Evaluation])
