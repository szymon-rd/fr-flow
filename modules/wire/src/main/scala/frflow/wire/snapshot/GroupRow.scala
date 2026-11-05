package frflow.wire.snapshot

import io.circe.Codec

/** One consistency obligation: the statements in it, what is open and provided, each witness in words, and how it
  * stands (`proven`, `evidence: …`, `not-proven`).
  */
final case class GroupRow(statements: List[String], open: List[String], provided: List[String],
    witnesses: List[String], standing: String) derives Codec.AsObject
