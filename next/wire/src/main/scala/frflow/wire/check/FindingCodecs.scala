package frflow.wire.check

import cats.syntax.all.*
import frflow.core.expr.Value
import frflow.proof.obligation.TryKind
import frflow.proof.reading.{Diagnostic, NotAllowed}
import frflow.proof.verdict.Finding
import frflow.wire.check.ObligationNames.given
import frflow.wire.file.Tagged
import frflow.wire.test.ValueCodecs.given
import io.circe.syntax.*
import io.circe.{Decoder, Encoder, HCursor, Json}

/** Why a check ended where it did, and Lean's messages, as `checks.json` writes them. */
object FindingCodecs:
  given Encoder[Diagnostic] = Encoder.instance(d => Json.obj("file" -> d.file.asJson, "line" -> d.line.asJson,
    "error" -> d.error.asJson, "message" -> d.message.asJson))
  given Decoder[Diagnostic] = Decoder.instance(c => (c.get[String]("file"), c.get[Int]("line"),
    c.get[Boolean]("error"), c.get[String]("message")).mapN(Diagnostic(_, _, _, _)))

  given Encoder[Finding] = Encoder.instance {
    case Finding.LeanTimedOut            => Tagged("lean-timed-out")
    case Finding.ModelDoesNotBuild(es)   => Tagged("model-does-not-build", "errors" -> es.asJson)
    case Finding.ProofNotAllowed(what)   => Tagged("proof-not-allowed", "what" -> Json.fromValues(what.map((l, r) =>
                                              Json.obj("line" -> l.asJson, "rule" -> NotAllowedCodecs.encode(r)))))
    case Finding.LemmasDoNotBuild(es)    => Tagged("lemmas-do-not-build", "errors" -> es.asJson)
    case Finding.NotProven(es)           => Tagged("not-proven", "errors" -> es.asJson)
    case Finding.Refuted(tries)          => Tagged("refuted", "tries" -> tries.asJson)
    case Finding.DisallowedAxioms(axioms) => Tagged("disallowed-axioms", "axioms" -> axioms.asJson)
    case Finding.StepRefuted(inputs)     => Tagged("step-refuted", "inputs" -> Json.fromValues(inputs.map((n, v) =>
                                              Json.obj("name" -> n.asJson, "value" -> v.asJson))))
  }

  given Decoder[Finding] = Tagged.decoder("finding") {
    case "lean-timed-out"       => _ => Right(Finding.LeanTimedOut)
    case "model-does-not-build" => errors(_).map(Finding.ModelDoesNotBuild(_))
    case "proof-not-allowed"    => _.get[List[(Int, NotAllowed)]]("what")(using Decoder.decodeList(using rule))
                                     .map(Finding.ProofNotAllowed(_))
    case "lemmas-do-not-build"  => errors(_).map(Finding.LemmasDoNotBuild(_))
    case "not-proven"           => errors(_).map(Finding.NotProven(_))
    case "refuted"              => _.get[List[TryKind]]("tries").map(Finding.Refuted(_))
    case "disallowed-axioms"    => _.get[List[String]]("axioms").map(Finding.DisallowedAxioms(_))
    case "step-refuted"         => _.get[List[(String, Value)]]("inputs")(using Decoder.decodeList(using input))
                                     .map(Finding.StepRefuted(_))
  }

  private val input: Decoder[(String, Value)] = Decoder.instance(c =>
    (c.get[String]("name"), c.get[Value]("value")).tupled)

  private def errors(c: HCursor) = c.get[List[Diagnostic]]("errors")

  private val rule: Decoder[(Int, NotAllowed)] = Decoder.instance(c =>
    (c.get[Int]("line"), c.get[NotAllowed]("rule")(using NotAllowedCodecs.decoder)).tupled)
