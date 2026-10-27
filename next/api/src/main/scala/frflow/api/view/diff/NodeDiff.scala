package frflow.api.view.diff

/** What moved under a node's decision: its own fields' line diffs, what it rests on whose meaning moved (nearest
  * first, each with its fields' diffs since then), its parts added and removed, and its governed code's diff since
  * the decision's commit. Never decided: nothing moved under a decision, and its code in full is the front end's to
  * read.
  */
final case class NodeDiff(fields: List[FieldDiff], above: List[Moved], parts: Parts, code: Option[String])
