package frflow.api.view

import frflow.core.name.NodeId

/** Where a change belongs: the nodes whose words mention it, and the nodes governing a path. */
final case class Found(mentioning: List[NodeId], governing: List[NodeId])
