package frflow.wire.test

import cats.syntax.all.*
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.expr.Value
import frflow.core.ty.Ty
import frflow.eval.EvalError
import frflow.testing.Seed
import frflow.testing.report.*
import frflow.wire.file.Names.given
import frflow.wire.file.Tagged
import frflow.wire.test.BrokenCodecs.given
import frflow.wire.test.FailureCodecs.given
import frflow.wire.test.TyCodecs.given
import frflow.wire.test.ValueCodecs.given
import io.circe.syntax.*
import io.circe.{ACursor, Decoder, Encoder, Json, JsonObject}

/** What testing a node's code found: how many cases were asked and tried from which seed, against what, the outcome
  * (passed, the smallest failing case, or not checked and why), the parts no case reached, and the notes (each
  * given generator and what it makes, the examples' values one never makes, nothing to vary).
  */
object ReportCodecs:
  given Encoder[Against] = Encoder.instance {
    case Against.Claim(n)    => Tagged("claim", "node" -> n.asJson)
    case Against.Model(n, m) => Tagged("model", "node" -> n.asJson, "model" -> m.asJson)
  }

  given Decoder[Against] = Tagged.decoder("test target") {
    case "claim" => _.get[NodeId]("node").map(Against.Claim(_))
    case "model" => c => (c.get[NodeId]("node"), c.get[ModelName]("model")).mapN(Against.Model(_, _))
  }

  given Encoder[Outcome] = Encoder.instance {
    case Outcome.Passed        => Tagged("passed")
    case Outcome.Failed(f)     => Tagged("failed", "failure" -> f.asJson)
    case Outcome.NotChecked(e) => Tagged("not-checked", "error" -> e.asJson)
  }

  given Decoder[Outcome] = Tagged.decoder("outcome") {
    case "passed"      => _ => Right(Outcome.Passed)
    case "failed"      => _.get[Failure]("failure").map(Outcome.Failed(_))
    case "not-checked" => _.get[EvalError]("error").map(Outcome.NotChecked(_))
  }

  given Encoder[Reach] = Encoder.instance {
    case Reach.Premise   => Tagged("premise")
    case Reach.Side(i)   => Tagged("side", "index" -> i.asJson)
    case Reach.Branch(h) => Tagged("branch", "held" -> h.asJson)
    case Reach.Arm(i)    => Tagged("arm", "index" -> i.asJson)
    case Reach.NonEmpty  => Tagged("non-empty")
    case Reach.Called(o) => Tagged("called", "op" -> o.asJson)
  }

  given Decoder[Reach] = Tagged.decoder("reach") {
    case "premise"   => _ => Right(Reach.Premise)
    case "side"      => _.get[Int]("index").map(Reach.Side(_))
    case "branch"    => _.get[Boolean]("held").map(Reach.Branch(_))
    case "arm"       => _.get[Int]("index").map(Reach.Arm(_))
    case "non-empty" => _ => Right(Reach.NonEmpty)
    case "called"    => _.get[SymbolName]("op").map(Reach.Called(_))
  }

  given Encoder[Target] = Encoder.instance(t => Json.obj("path" -> t.at.path.asJson, "reach" -> t.reach.asJson))
  given Decoder[Target] = Decoder.instance(c =>
    (c.get[List[Int]]("path").map(Position(_)), c.get[Reach]("reach")).mapN(Target(_, _)))

  given Encoder[Note] = Encoder.instance {
    case Note.Given(m)          => Tagged("given", "type" -> m.ty.asJson, "says" -> m.says.asJson)
    case Note.NeverMade(ty, vs) => Tagged("never-made", "type" -> ty.asJson, "values" -> vs.asJson)
    case Note.NothingToVary     => Tagged("nothing-to-vary")
  }

  given Decoder[Note] = Tagged.decoder("note") {
    case "given"           => c => (c.get[Ty]("type"), c.get[Option[String]]("says"))
                                .mapN((t, s) => Note.Given(Made(t, s)))
    case "never-made"      => c => (c.get[Ty]("type"), c.get[List[Value]]("values")).mapN(Note.NeverMade(_, _))
    case "nothing-to-vary" => _ => Right(Note.NothingToVary)
  }

  def encode(r: TestReport): JsonObject = JsonObject("asked" -> r.count.asked.asJson, "cases" -> r.cases.asJson,
    "seed" -> r.seed.asJson, "against" -> r.against.asJson, "outcome" -> r.outcome.asJson,
    "unreached" -> r.unreached.asJson, "notes" -> r.notes.asJson)

  def decode(c: ACursor): Decoder.Result[TestReport] =
    ((c.get[Int]("asked"), c.get[Int]("cases")).mapN(Count(_, _)), c.get[Seed]("seed"),
      c.get[Against]("against"), c.get[Outcome]("outcome"), c.get[List[Target]]("unreached"),
      c.get[List[Note]]("notes")).mapN(TestReport(_, _, _, _, _, _))
