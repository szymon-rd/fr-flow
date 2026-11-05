package frflow.wire.snapshot

import io.circe.Codec

/** One obligation: its theorem's name, what Lean found, and its statement as generated. */
final case class ObligationRow(name: String, status: String, statement: String) derives Codec.AsObject
