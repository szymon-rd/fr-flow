package frflow.api.view.whole

import frflow.api.node.lean.ObligationView
import frflow.core.name.NodeId

/** An `always(stored)` and the assumption saying what state the store starts in (none: nothing says it, so Lean is
  * asked nothing and it is not proven), with Lean's outcome of `start_<node>`: every such state meets it.
  */
final case class StartView(statement: NodeId, start: Option[NodeId], check: ObligationView)
