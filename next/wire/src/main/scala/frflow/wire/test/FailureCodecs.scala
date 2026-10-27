package frflow.wire.test

import cats.syntax.all.*
import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.core.name.{BoundaryName, OpName}
import frflow.eval.ScalaValue
import frflow.eval.run.Broken
import frflow.testing.Seed
import frflow.testing.model.{Difference, Step}
import frflow.testing.report.{Drawn, Failure}
import frflow.wire.file.Names.given
import frflow.wire.file.Tagged
import frflow.wire.test.BrokenCodecs.given
import frflow.wire.test.ValueCodecs.given
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder, HCursor, Json}

/** A failing case, and where it was drawn (its seed, index and size draw it again). A model test's calls and answers
  * are Scala values, untyped: they are written as Scala prints them and read back as that text.
  */
object FailureCodecs:
  given Encoder[ScalaValue] = Encoder.encodeString.contramap(v => String.valueOf(v.unwrap))
  given Decoder[ScalaValue] = Decoder.decodeString.map(ScalaValue(_))

  /** A seed as a whole number written as a string: it names a run, and a reader that rounds numbers keeps it. */
  given Codec[Seed] = Codec.from(
    Decoder.decodeString.emap(s => s.toLongOption.map(Seed(_)).toRight("not a seed (a whole number, as a string)")),
    Encoder.encodeString.contramap(_.value.toString))

  given Encoder[Drawn] = Encoder.instance(d =>
    Json.obj("seed" -> d.seed.asJson, "index" -> d.index.asJson, "size" -> d.size.asJson))
  given Decoder[Drawn] = Decoder.instance(c =>
    (c.get[Seed]("seed"), c.get[Int]("index"), c.get[Int]("size")).mapN(Drawn(_, _, _)))

  given Encoder[Step] = Encoder.instance(s =>
    Json.obj("boundary" -> s.boundary.asJson, "op" -> s.op.asJson, "args" -> s.args.asJson))
  given Decoder[Step] = Decoder.instance(c =>
    (c.get[BoundaryName]("boundary"), c.get[OpName]("op"), c.get[List[ScalaValue]]("args")).mapN(Step(_, _, _)))

  given Encoder[Difference] = Encoder.instance {
    case Difference.Answer(s, i, m) => Tagged("answer", "step" -> s.asJson, "implementation" -> i.asJson,
                                         "model" -> m.asJson)
    case Difference.State(i, m)     => Tagged("state", "implementation" -> i.asJson, "model" -> m.asJson)
    case Difference.Threw(message)  => Tagged("threw", "message" -> message.asJson)
  }

  given Decoder[Difference] = Tagged.decoder("difference") {
    case "answer" => c => (c.get[Step]("step"), parted(c)).mapN((s, im) => Difference.Answer(s, im._1, im._2))
    case "state"  => parted(_).map(Difference.State(_, _))
    case "threw"  => _.get[String]("message").map(Difference.Threw(_))
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
    case "run"  => c => (c.get[Value]("start"), c.get[List[Step]]("steps"), c.get[Difference]("difference"),
                     c.get[Drawn]("from")).mapN(Failure.Run(_, _, _, _))
  }

  private def parted(c: HCursor): Decoder.Result[(ScalaValue, ScalaValue)] =
    (c.get[ScalaValue]("implementation"), c.get[ScalaValue]("model")).tupled
