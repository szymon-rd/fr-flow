package frflow.wire.snapshot

/** How a node's code is shown, piece by piece: the define Lean proves, what is tested, what is assumed. */
final case class CodeRow(proven: Option[String], tested: List[String], assumed: List[String])
