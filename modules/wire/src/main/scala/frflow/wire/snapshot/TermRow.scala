package frflow.wire.snapshot

import io.circe.Codec

/** A term of the vocabulary and what it means. */
final case class TermRow(name: String, means: String) derives Codec.AsObject
