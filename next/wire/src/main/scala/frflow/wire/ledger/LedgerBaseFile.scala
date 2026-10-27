package frflow.wire.ledger

import cats.syntax.all.*
import frflow.decision.ledger.LedgerBase
import frflow.wire.file.FileFormat
import io.circe.syntax.*
import io.circe.{Decoder, Encoder, JsonObject}

/** `.frflow/ledger-base`: one version of where the ledger's committed history is read from (its committed versions are
  * its history in git): the version it follows (absent for the first), the SHA-256 of the ledger file's text it
  * accepts, and its seal. A seal that is missing or partly written reads as none, so `LedgerBase.committed` refuses it.
  */
object LedgerBaseFile:
  val format: FileFormat[LedgerBase] = FileFormat(".frflow/ledger-base", 1, encoder, decoder)

  private def encoder: Encoder.AsObject[LedgerBase] = Encoder.AsObject.instance(b => JsonObject("after" -> b.after.asJson,
    "ledger" -> b.ledger.asJson, "seal" -> b.seal.map(SealCodecs.encode).asJson))

  private def decoder: Decoder[LedgerBase] = Decoder.instance(c =>
    (c.get[String]("ledger"), c.get[Option[String]]("after"))
      .mapN((ledger, after) => LedgerBase(ledger, after, SealCodecs.optional(c.downField("seal")))))
