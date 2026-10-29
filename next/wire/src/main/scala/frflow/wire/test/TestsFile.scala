package frflow.wire.test

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.testing.report.{Failure, TestReport}
import frflow.wire.file.FileFormat
import frflow.wire.test.FailureCodecs.given
import io.circe.syntax.*
import io.circe.{ACursor, Decoder, Encoder, HCursor, Json, JsonObject}

/** The tests' two files, nodes in the order of their ids: `.frflow/tests.json` (not committed), each node's report
  * with the key it is current for (`key` first, then the report's fields); `.frflow/counterexamples.json`
  * (committed), each node's failing cases, replayed first. Version 2: a model test's step is its operation (no
  * boundary), and a model's runs name the model (no realization); version 1 is still read.
  */
object TestsFile:
  val format: FileFormat[Map[NodeId, (String, TestReport)]] = FileFormat(".frflow/tests.json", 2,
    byNode("tests")((k, r) => Json.fromJsonObject(("key" -> k.asJson) +: ReportCodecs.encode(r))),
    readByNode("tests")(c => (c.get[String]("key"), ReportCodecs.decode(c)).tupled),
    Map(1 -> readByNode("tests")(c => (c.get[String]("key"), ReportCodecs.decodeV1(c)).tupled)))

  /** A version 1 step's boundary is left unread: its operation names it. */
  val counterexamples: FileFormat[Map[NodeId, List[Failure]]] = FileFormat(".frflow/counterexamples.json", 2,
    byNode("counterexamples")(_.asJson), readByNode("counterexamples")(_.as[List[Failure]]),
    Map(1 -> readByNode("counterexamples")(_.as[List[Failure]])))

  private def byNode[A](name: String)(encode: A => Json): Encoder.AsObject[Map[NodeId, A]] =
    Encoder.AsObject.instance(m => JsonObject(name -> Json.fromFields(m.toList.sortBy(_._1).map((id, a) =>
      id.value -> encode(a)))))

  private def readByNode[A](name: String)(decode: ACursor => Decoder.Result[A]): Decoder[Map[NodeId, A]] =
    Decoder.instance((c: HCursor) => c.get[JsonObject](name).flatMap(_.keys.toList.traverse(k =>
      decode(c.downField(name).downField(k)).map(NodeId(k) -> _))).map(_.toMap))
