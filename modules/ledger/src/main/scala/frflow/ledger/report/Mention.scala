package frflow
package ledger
package report

import io.circe.Codec

/** A mention, with its sentence that holds a word asked for. */
final case class Mention(what: Mentioned, sentence: Option[String]) derives Codec.AsObject
