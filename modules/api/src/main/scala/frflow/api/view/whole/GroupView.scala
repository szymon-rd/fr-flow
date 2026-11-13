package frflow.api.view.whole

import frflow.api.node.proving.ObligationView
import frflow.core.consistency.Witness
import frflow.core.name.NodeId

/** One consistency group as `status` and `show` print it: its statements, the witness of each open value, how it
  * stands, and Rocq's outcome of its `consistent_<i>` with Rocq's messages.
  */
final case class GroupView(statements: List[NodeId], witnesses: List[Witness], status: GroupStatus,
    check: ObligationView)
