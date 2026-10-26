package frflow.api.node

import frflow.core.name.NodeId

/** One node as front ends show it, by concept; it replaces today's `NodeDetails` (19 fields) and the view's half of
  * `SnapNode` (31).
  */
final case class NodeView(id: NodeId, says: Says, place: Placement, proof: ProofView, code: Option[CodeView],
    review: ReviewView)
