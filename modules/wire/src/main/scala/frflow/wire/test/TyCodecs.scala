package frflow.wire.test

import frflow.core.name.TypeName
import frflow.core.ty.{NumKind, Ty}
import frflow.wire.file.Names.given
import frflow.wire.file.{Tagged, Words}
import io.circe.syntax.*
import io.circe.{Codec, Decoder, Encoder, HCursor, Json}

/** A type, as the tests' report names the types its generators make: by its kind, with the types it is made of. */
object TyCodecs:
  given Codec[NumKind] = Words.codec("number kind", NumKind.values) {
    case NumKind.Int32 => "int32"
    case NumKind.Int64 => "int64"
    case NumKind.Big   => "big"
  }

  given Encoder[Ty] = Encoder.instance(encode)
  given Decoder[Ty] = Tagged.decoder("type")(cases)

  private def encode(t: Ty): Json = t match
    case Ty.Bool           => Tagged("bool")
    case Ty.Str            => Tagged("str")
    case Ty.Unit           => Tagged("unit")
    case Ty.World          => Tagged("world")
    case Ty.Never          => Tagged("never")
    case Ty.Num(k)         => Tagged("num", "num" -> k.asJson)
    case Ty.ListOf(a)      => Tagged("list", "elem" -> a.asJson)
    case Ty.OptionOf(a)    => Tagged("option", "elem" -> a.asJson)
    case Ty.EitherOf(e, a) => Tagged("either", "error" -> e.asJson, "value" -> a.asJson)
    case Ty.MapOf(k, v)    => Tagged("map", "key" -> k.asJson, "value" -> v.asJson)
    case Ty.SetOf(a)       => Tagged("set", "elem" -> a.asJson)
    case Ty.TupleOf(as)    => Tagged("tuple", "elems" -> as.asJson)
    case Ty.FnOf(ps, r)    => Tagged("fn", "params" -> ps.asJson, "result" -> r.asJson)
    case Ty.Sort(n)        => Tagged("sort", "name" -> n.asJson)
    case Ty.Data(n)        => Tagged("data", "name" -> n.asJson)
    case Ty.FlowOf(r, e)   => Tagged("flow", "result" -> r.asJson, "error" -> e.asJson)

  private def cases: PartialFunction[String, HCursor => Decoder.Result[Ty]] = {
    case "bool"   => _ => Right(Ty.Bool)
    case "str"    => _ => Right(Ty.Str)
    case "unit"   => _ => Right(Ty.Unit)
    case "world"  => _ => Right(Ty.World)
    case "never"  => _ => Right(Ty.Never)
    case "num"    => _.get[NumKind]("num").map(Ty.Num(_))
    case "list"   => _.get[Ty]("elem").map(Ty.ListOf(_))
    case "option" => _.get[Ty]("elem").map(Ty.OptionOf(_))
    case "either" => c => c.get[Ty]("error").flatMap(e => c.get[Ty]("value").map(Ty.EitherOf(e, _)))
    case "map"    => c => c.get[Ty]("key").flatMap(k => c.get[Ty]("value").map(Ty.MapOf(k, _)))
    case "set"    => _.get[Ty]("elem").map(Ty.SetOf(_))
    case "tuple"  => _.get[List[Ty]]("elems").map(Ty.TupleOf(_))
    case "fn"     => c => c.get[List[Ty]]("params").flatMap(ps => c.get[Ty]("result").map(Ty.FnOf(ps, _)))
    case "sort"   => _.get[TypeName]("name").map(Ty.Sort(_))
    case "data"   => _.get[TypeName]("name").map(Ty.Data(_))
    case "flow"   => c => c.get[Ty]("result").flatMap(r => c.get[Option[Ty]]("error").map(Ty.FlowOf(r, _)))
  }
