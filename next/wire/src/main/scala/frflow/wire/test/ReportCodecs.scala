package frflow.wire.test

import cats.syntax.all.*
import frflow.core.name.{DefName, NodeId}
import frflow.core.ty.Ty
import frflow.testing.Seed
import frflow.testing.report.{Against, Failure, Made, Position, TestReport}
import frflow.wire.file.Names.given
import frflow.wire.file.Tagged
import frflow.wire.test.FailureCodecs.given
import frflow.wire.test.TyCodecs.given
import io.circe.syntax.*
import io.circe.{ACursor, Decoder, Encoder, Json, JsonObject}

/** What testing a node's code found: how many cases from which seed, against what, the smallest failing case, the
  * conditions no case reached (by their index), and what each given generator makes.
  */
object ReportCodecs:
  given Encoder[Against] = Encoder.instance {
    case Against.Claim(n)    => Tagged("claim", "node" -> n.asJson)
    case Against.Define(d)   => Tagged("define", "define" -> d.asJson)
    case Against.Model(n, i) => Tagged("model", "node" -> n.asJson, "realization" -> i.asJson)
  }

  given Decoder[Against] = Tagged.decoder("test target") {
    case "claim"  => _.get[NodeId]("node").map(Against.Claim(_))
    case "define" => _.get[DefName]("define").map(Against.Define(_))
    case "model"  => c => (c.get[NodeId]("node"), c.get[Int]("realization")).mapN(Against.Model(_, _))
  }

  given Encoder[Made] = Encoder.instance(m => Json.obj("type" -> m.ty.asJson, "says" -> m.says.asJson))
  given Decoder[Made] = Decoder.instance(c => (c.get[Ty]("type"), c.get[Option[String]]("says")).mapN(Made(_, _)))

  def encode(r: TestReport): JsonObject = JsonObject("cases" -> r.cases.asJson, "seed" -> r.seed.asJson,
    "against" -> r.against.asJson, "failure" -> r.failure.asJson, "unreached" -> r.unreached.map(_.condition).asJson,
    "made" -> r.made.asJson)

  def decode(c: ACursor): Decoder.Result[TestReport] =
    (c.get[Int]("cases"), c.get[Seed]("seed"), c.get[Against]("against"),
      c.get[Option[Failure]]("failure"), c.get[List[Int]]("unreached").map(_.map(Position(_))),
      c.get[List[Made]]("made")).mapN(TestReport(_, _, _, _, _, _))
