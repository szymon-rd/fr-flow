package frflow.wire.test

import cats.syntax.all.*
import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.eval.run.Broken
import frflow.testing.report.{Drawn, Failure}
import frflow.testing.report.Seed
import frflow.wire.file.Tagged
import frflow.wire.test.BrokenCodecs.given
import frflow.wire.test.ValueCodecs.given
import io.circe.{Codec, Decoder, Encoder, Json}
import io.circe.syntax.*

/** A failing case, and where it was drawn (its seed, index and size draw it again). */
object FailureCodecs:
  /** A seed as a whole number written as a string: it names a run, and a reader that rounds numbers keeps it. */
  given Codec[Seed] = Codec.from(
    Decoder.decodeString.emap(s => s.toLongOption.map(Seed(_)).toRight("not a seed (a whole number, as a string)")),
    Encoder.encodeString.contramap(_.value.toString))

  given Encoder[Drawn] = Encoder.instance(d =>
    Json.obj("seed" -> d.seed.asJson, "index" -> d.index.asJson, "size" -> d.size.asJson))
  given Decoder[Drawn] = Decoder.instance(c =>
    (c.get[Seed]("seed"), c.get[Int]("index"), c.get[Int]("size")).mapN(Drawn(_, _, _)))

  given Encoder[Failure] = Encoder.instance(f => Tagged("call", "inputs" -> f.inputs.asJson,
    "givens" -> f.givens.asJson, "broke" -> f.broke.asJson, "from" -> f.from.asJson))

  given Decoder[Failure] = Tagged.decoder("failure") {
    case "call" => c => (c.get[List[Value]]("inputs"), c.get[List[Given]]("givens"), c.get[Broken]("broke"),
                     c.get[Drawn]("from")).mapN(Failure(_, _, _, _))
  }
