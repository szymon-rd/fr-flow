package frflow.wire.ledger

import cats.syntax.all.*
import frflow.decision.ledger.{Decider, Deciders}
import frflow.wire.file.FileFormat
import io.circe.syntax.*
import io.circe.{Decoder, Encoder, JsonObject}

/** `.frflow/deciders`: one version of who may decide (the committed versions are its history in git): the version
  * it follows (absent for the first), the deciders in their order, and its seal. A seal that is missing or partly
  * written reads as one no key verifies, so the list reads and `Deciders.committed` refuses it.
  */
object DecidersFile:
  val format: FileFormat[Deciders] = FileFormat(".frflow/deciders", 1, encoder, decoder)

  private given Encoder.AsObject[Decider] = Encoder.AsObject.instance(d =>
    JsonObject("name" -> d.name.asJson, "key" -> d.key.asJson, "publicKey" -> d.publicKey.asJson))

  private given Decoder[Decider] = Decoder.instance(c =>
    (c.get[String]("name"), c.get[String]("key"), c.get[String]("publicKey")).mapN(Decider(_, _, _)))

  private def encoder: Encoder.AsObject[Deciders] = Encoder.AsObject.instance(d =>
    JsonObject("after" -> d.after.asJson, "deciders" -> d.entries.asJson, "seal" -> SealCodecs.encode(d.seal)))

  private def decoder: Decoder[Deciders] = Decoder.instance(c =>
    (c.get[List[Decider]]("deciders"), c.get[Option[String]]("after"))
      .mapN((entries, after) => Deciders(entries, after, SealCodecs.orUnsigned(c.downField("seal")))))
