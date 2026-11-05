package frflow.api.view

import frflow.api.node.NodeView
import frflow.api.view.whole.WholeView
import frflow.core.name.NodeId

/** Everything a front end shows, derived once from the analysis: each node's view in decision order, the root
  * statements, the theory as a whole (consistency, vacuity, examples), the overview, the warnings `status` fails on,
  * and the decided nodes no longer in the model. The front ends see this, never the analysis.
  */
final case class View(nodes: List[NodeView], roots: List[NodeId], whole: WholeView, overview: Overview,
    warnings: List[Warning], gone: List[NodeId]):
  def node(id: NodeId): Option[NodeView] = nodes.find(_.id == id)
