package frflow.api.view.diff

import frflow.core.name.NodeId

/** A node's parts added and removed since its decision. */
final case class Parts(added: List[NodeId], removed: List[NodeId])
