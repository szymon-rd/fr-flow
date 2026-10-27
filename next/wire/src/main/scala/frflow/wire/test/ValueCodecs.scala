package frflow.wire.test

import cats.syntax.all.*
import frflow.core.example.Given
import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, ModelName, SymbolName}
import frflow.wire.file.Names.given
import frflow.wire.file.{Tagged, Words}
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder, HCursor, Json}

/** A value of the term language (a failing case's inputs and state), by its kind; numbers exactly, as JSON numbers. */
object ValueCodecs:
  given Codec[Side] = Words.codec("side", Side.values) {
    case Side.Error => "error"
    case Side.Value => "value"
  }

  given Encoder[Value] = Encoder.instance(encode)
  given Decoder[Value] = Tagged.decoder("value")(cases)

  private def encode(v: Value): Json = v match
    case Value.Bool(b)       => Tagged("bool", "value" -> b.asJson)
    case Value.Num(n)        => Tagged("num", "value" -> n.asJson)
    case Value.Str(s)        => Tagged("str", "value" -> s.asJson)
    case Value.Unit          => Tagged("unit")
    case Value.Data(c, fs)   => Tagged("data", "ctor" -> c.asJson, "fields" -> fs.asJson)
    case Value.Many(xs)      => Tagged("many", "elems" -> xs.asJson)
    case Value.Maybe(x)      => Tagged("maybe", "elem" -> x.asJson)
    case Value.Pairs(es)     => Tagged("pairs", "entries" -> Json.fromValues(es.map((k, v) =>
                                  Json.obj("key" -> k.asJson, "value" -> v.asJson))))
    case Value.Tuple(xs)     => Tagged("tuple", "elems" -> xs.asJson)
    case Value.Inject(s, x)  => Tagged("inject", "side" -> s.asJson, "elem" -> x.asJson)
    case Value.World(ss, fs) => Tagged("world", "states" -> Json.fromValues(ss.map((m, s) =>
                                  Json.obj("model" -> m.asJson, "state" -> s.asJson))), "faults" -> fs.asJson)

  private def cases: PartialFunction[String, HCursor => Decoder.Result[Value]] = {
    case "bool"   => _.get[Boolean]("value").map(Value.Bool(_))
    case "num"    => _.get[BigInt]("value").map(Value.Num(_))
    case "str"    => _.get[String]("value").map(Value.Str(_))
    case "unit"   => _ => Right(Value.Unit)
    case "data"   => c => (c.get[CtorName]("ctor"), c.get[List[Value]]("fields")).mapN(Value.Data(_, _))
    case "many"   => _.get[List[Value]]("elems").map(Value.Many(_))
    case "maybe"  => _.get[Option[Value]]("elem").map(Value.Maybe(_))
    case "pairs"  => _.get[List[(Value, Value)]]("entries")(using Decoder.decodeList(using entry)).map(Value.Pairs(_))
    case "tuple"  => _.get[List[Value]]("elems").map(Value.Tuple(_))
    case "inject" => c => (c.get[Side]("side"), c.get[Value]("elem")).mapN(Value.Inject(_, _))
    case "world"  => c => (c.get[List[(ModelName, Value)]]("states")(using Decoder.decodeList(using state)),
                       c.get[List[Boolean]]("faults")).mapN(Value.World(_, _))
  }

  given Encoder[Given] = Encoder.instance(g => Json.obj("symbol" -> g.symbol.asJson, "value" -> g.value.asJson))
  given Decoder[Given] = Decoder.instance(c => (c.get[SymbolName]("symbol"), c.get[Value]("value")).mapN(Given(_, _)))

  private def entry: Decoder[(Value, Value)] =
    Decoder.instance(c => (c.get[Value]("key"), c.get[Value]("value")).tupled)
  private def state: Decoder[(ModelName, Value)] =
    Decoder.instance(c => (c.get[ModelName]("model"), c.get[Value]("state")).tupled)
