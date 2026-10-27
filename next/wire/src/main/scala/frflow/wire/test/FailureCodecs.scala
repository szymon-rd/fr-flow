package frflow.wire.test

import cats.syntax.all.*
import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.core.name.{BoundaryName, OpName}
import frflow.eval.run.Broken
import frflow.testing.Seed
import frflow.testing.model.{Difference, Ran, Step}
import frflow.testing.report.{Drawn, Failure}
import frflow.wire.file.Names.given
import frflow.wire.file.Tagged
import frflow.wire.test.BrokenCodecs.given
import frflow.wire.test.ValueCodecs.given
import io.circe.syntax.*
import io.circe.{Decoder, Encoder, HCursor, Json}

/** A failing case, and where it was drawn (its seed, index and size draw it again); a model test's calls and what
  * each did, as data.
  */
object FailureCodecs:
  given Encoder[Drawn] = Encoder.instance(d =>
    Json.obj("seed" -> d.seed.value.asJson, "index" -> d.index.asJson, "size" -> d.size.asJson))
  given Decoder[Drawn] = Decoder.instance(c =>
    (c.get[Long]("seed").map(Seed(_)), c.get[Int]("index"), c.get[Int]("size")).mapN(Drawn(_, _, _)))

  given Encoder[Step] = Encoder.instance(s =>
    Json.obj("boundary" -> s.boundary.asJson, "op" -> s.op.asJson, "args" -> s.args.asJson))
  given Decoder[Step] = Decoder.instance(c =>
    (c.get[BoundaryName]("boundary"), c.get[OpName]("op"), c.get[List[Value]]("args")).mapN(Step(_, _, _)))

  given Encoder[Ran] = Encoder.instance {
    case Ran.Gave(v)   => Tagged("gave", "result" -> v.asJson)
    case Ran.Failed(e) => Tagged("failed", "error" -> e.asJson)
    case Ran.Threw(m)  => Tagged("threw", "message" -> m.asJson)
  }

  given Decoder[Ran] = Tagged.decoder("call") {
    case "gave"   => _.get[Value]("result").map(Ran.Gave(_))
    case "failed" => _.get[Value]("error").map(Ran.Failed(_))
    case "threw"  => _.get[String]("message").map(Ran.Threw(_))
  }

  given Encoder[Difference] = Encoder.instance {
    case Difference.Call(s, i, m)   => Tagged("call", "step" -> s.asJson, "implementation" -> i.asJson,
                                         "model" -> m.asJson)
    case Difference.State(i, m)     => Tagged("state", "implementation" -> i.asJson, "model" -> m.asJson)
    case Difference.NotRun(message) => Tagged("not-run", "message" -> message.asJson)
  }

  given Decoder[Difference] = Tagged.decoder("difference") {
    case "call"    => c => (c.get[Step]("step"), c.get[Ran]("implementation"), c.get[Ran]("model"))
                       .mapN(Difference.Call(_, _, _))
    case "state"   => c => (c.get[Value]("implementation"), c.get[Value]("model")).mapN(Difference.State(_, _))
    case "not-run" => _.get[String]("message").map(Difference.NotRun(_))
  }

  given Encoder[Failure] = Encoder.instance {
    case Failure.Call(inputs, givens, broke, from) =>
      Tagged("call", "inputs" -> inputs.asJson, "givens" -> givens.asJson, "broke" -> broke.asJson,
        "from" -> from.asJson)
    case Failure.Run(start, steps, difference, from) =>
      Tagged("run", "start" -> start.asJson, "steps" -> steps.asJson, "difference" -> difference.asJson,
        "from" -> from.asJson)
  }

  given Decoder[Failure] = Tagged.decoder("failure") {
    case "call" => c => (c.get[List[Value]]("inputs"), c.get[List[Given]]("givens"), c.get[Broken]("broke"),
                     c.get[Drawn]("from")).mapN(Failure.Call(_, _, _, _))
    case "run"  => c => run(c)
  }

  private def run(c: HCursor): Decoder.Result[Failure] =
    (c.get[Value]("start"), c.get[List[Step]]("steps"), c.get[Difference]("difference"), c.get[Drawn]("from"))
      .mapN(Failure.Run(_, _, _, _))
