package frflow.wire.check

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.proof.verdict.{CheckKey, CheckStatus, Checks, Finding, NodeCheck, Result, WholeCheck}
import frflow.wire.check.FindingCodecs.given
import frflow.wire.check.ResultCodecs.given
import frflow.wire.file.FileFormat
import io.circe.syntax.*
import io.circe.{ACursor, Decoder, Encoder, Json, JsonObject}
import java.time.Instant

/** `.frflow/checks.json` (not committed): each node's check, nodes in the order of their ids, by the key it is current
  * for: its status, each obligation's outcome, the findings, and when it was made; then the theory's own check
  * (`whole`: consistency, vacuity, the examples), by its key, absent before it is first made.
  */
object ChecksFile:
  val format: FileFormat[Checks] = FileFormat(".frflow/checks.json", 1, encoder, decoder)

  private def encoder: Encoder.AsObject[Checks] = Encoder.AsObject.instance(m =>
    JsonObject("checks" -> Json.fromFields(m.nodes.toList.sortBy(_._1).map((id, c) => id.value -> encode(c))),
      "whole" -> m.whole.map(whole).asJson))

  private def encode(c: NodeCheck): Json = Json.obj("key" -> c.key.value.asJson, "status" -> c.status.asJson,
    "results" -> c.results.asJson, "findings" -> c.findings.asJson, "at" -> c.at.asJson)

  private def whole(w: WholeCheck): Json =
    Json.obj("key" -> w.key.value.asJson, "results" -> w.results.asJson, "at" -> w.at.asJson)

  private def decoder: Decoder[Checks] = Decoder.instance(c =>
    (c.get[JsonObject]("checks").flatMap(_.keys.toList.traverse(k =>
      decode(NodeId(k), c.downField("checks").downField(k)).map(NodeId(k) -> _))).map(_.toMap),
      c.downField("whole").success.filterNot(_.value.isNull).traverse(readWhole)).mapN(Checks(_, _)))

  private def decode(node: NodeId, c: ACursor): Decoder.Result[NodeCheck] =
    (c.get[String]("key"), c.get[CheckStatus]("status"), c.get[List[Result]]("results"),
      c.get[List[Finding]]("findings"), c.get[Instant]("at"))
      .mapN((key, status, results, findings, at) => NodeCheck(node, CheckKey(key), status, results, findings, at))

  private def readWhole(c: ACursor): Decoder.Result[WholeCheck] =
    (c.get[String]("key"), c.get[List[Result]]("results"), c.get[Instant]("at"))
      .mapN((key, results, at) => WholeCheck(CheckKey(key), results, at))
