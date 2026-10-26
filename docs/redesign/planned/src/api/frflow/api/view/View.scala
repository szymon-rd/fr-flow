package frflow.api.view

import frflow.api.node.NodeView
import frflow.core.name.NodeId

/** Everything a front end shows, derived once from the analysis (`Views.of`): each node's view in decision order, the
  * root, the overview, and the warnings `status` fails on. The front ends see this, never the analysis.
  */
final case class View(nodes: List[NodeView], root: Option[NodeId], overview: Overview, warnings: List[Warning]):
  def node(id: NodeId): Option[NodeView] = nodes.find(_.id == id)
