package frflow.api.node

import frflow.core.name.NodeId

/** How deciding a node relates to the nodes around it: what it rests on whose meaning moved since it was decided
  * (nearest first), and the decisions below it that accepting it acts on (parents first).
  */
final case class Movement(above: List[NodeId], below: List[NodeId])
