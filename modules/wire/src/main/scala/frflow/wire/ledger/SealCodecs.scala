package frflow.wire.ledger

import cats.syntax.all.*
import frflow.decision.ledger.Seal
import io.circe.{ACursor, Json}

/** A signature as `{"key", "signature"}`. Read leniently: a seal that is missing, or lacks its key or its signature,
  * reads as none, so the file still reads and the decision rules refuse what it was meant to seal.
  */
object SealCodecs:
  def encode(s: Seal): Json = Json.obj("key" -> Json.fromString(s.key), "signature" -> Json.fromString(s.signature))

  def optional(c: ACursor): Option[Seal] = (c.get[String]("key"), c.get[String]("signature")).mapN(Seal(_, _)).toOption
