package frflow.wire.check

import cats.syntax.all.*
import frflow.proof.obligation.ObligationName
import frflow.proof.reading.Diagnostic
import frflow.proof.verdict.{CheckStatus, ObligationStatus, Result}
import frflow.wire.check.FindingCodecs.given
import frflow.wire.check.ObligationNames.given
import frflow.wire.file.Words
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder, Json}

/** A check's status, and each obligation's outcome: its name in Lean, its status, Lean's messages about it. */
object ResultCodecs:
  given Codec[ObligationStatus] = Words.codec("obligation status", ObligationStatus.values) {
    case ObligationStatus.Proven      => "proven"
    case ObligationStatus.Open        => "open"
    case ObligationStatus.Failed      => "failed"
    case ObligationStatus.Shown       => "shown"
    case ObligationStatus.NotShown    => "not-shown"
    case ObligationStatus.Unevaluated => "unevaluated"
    case ObligationStatus.Unchecked   => "unchecked"
    case ObligationStatus.Timeout     => "timeout"
  }

  given Codec[CheckStatus] = Words.codec("check status", CheckStatus.values) {
    case CheckStatus.Proven     => "proven"
    case CheckStatus.Open       => "open"
    case CheckStatus.Failed     => "failed"
    case CheckStatus.ModelError => "model-error"
    case CheckStatus.Waiting    => "waiting"
    case CheckStatus.Timeout    => "timeout"
    case CheckStatus.Unchecked  => "unchecked"
  }

  given Encoder[Result] = Encoder.instance(r =>
    Json.obj("name" -> r.name.asJson, "status" -> r.status.asJson, "messages" -> r.messages.asJson))
  given Decoder[Result] = Decoder.instance(c => (c.get[ObligationName]("name"), c.get[ObligationStatus]("status"),
    c.get[List[Diagnostic]]("messages")).mapN(Result(_, _, _)))
