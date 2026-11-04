package frflow.wire.snapshot

import io.circe.Codec

/** How a node's code is shown, piece by piece: the defines Lean proves, what is tested, what is assumed. */
final case class CodeRow(proven: List[String], tested: List[String], assumed: List[String]) derives Codec.AsObject
