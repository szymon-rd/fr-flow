package frflow.api.view

/** What moved under a node's decision: its fields' line diffs, what moved above it, its parts added and removed, and
  * its governed code's diff since the decision's commit.
  */
final case class NodeDiff(
    fields: List[(String, List[String])],
    above: List[String],
    parts: (List[String], List[String]),
    code: Option[String])
