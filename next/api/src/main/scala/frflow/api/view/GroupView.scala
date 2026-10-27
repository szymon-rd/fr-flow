package frflow.api.view

import frflow.core.consistency.Witness
import frflow.core.name.NodeId

/** One consistency group as `status` and `show` print it: its statements, the witness of each open value, and how
  * it stands.
  */
final case class GroupView(statements: List[NodeId], witnesses: List[Witness], status: GroupStatus)
