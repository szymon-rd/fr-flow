package frflow.wire.test

import frflow.core.name.{DefName, ModelName, NodeId, SymbolName}
import frflow.eval.EvalError
import frflow.eval.run.Broken
import frflow.wire.file.Names.given
import frflow.wire.file.Tagged
import io.circe.syntax.*
import io.circe.{Decoder, Encoder}

/** What a failing call broke, and why a term had no Scala value. */
object BrokenCodecs:
  given Encoder[EvalError] = Encoder.instance {
    case EvalError.Quantified  => Tagged("quantified")
    case EvalError.Unbound(s)  => Tagged("unbound", "symbol" -> s.asJson)
    case EvalError.NoDefine(d) => Tagged("no-define", "define" -> d.asJson)
    case EvalError.NoCase      => Tagged("no-case")
    case EvalError.NoModel(m)  => Tagged("no-model", "model" -> m.asJson)
    case EvalError.Steps       => Tagged("steps")
  }

  given Decoder[EvalError] = Tagged.decoder("evaluation error") {
    case "quantified" => _ => Right(EvalError.Quantified)
    case "unbound"    => _.get[SymbolName]("symbol").map(EvalError.Unbound(_))
    case "no-define"  => _.get[DefName]("define").map(EvalError.NoDefine(_))
    case "no-case"    => _ => Right(EvalError.NoCase)
    case "no-model"   => _.get[ModelName]("model").map(EvalError.NoModel(_))
    case "steps"      => _ => Right(EvalError.Steps)
  }

  given Encoder[Broken] = Encoder.instance {
    case Broken.Post            => Tagged("post")
    case Broken.Always(id)      => Tagged("always", "node" -> id.asJson)
    case Broken.Assumption(id)  => Tagged("assumption", "node" -> id.asJson)
    case Broken.NotEvaluated(e) => Tagged("not-evaluated", "error" -> e.asJson)
    case Broken.Threw(m)        => Tagged("threw", "message" -> m.asJson)
  }

  given Decoder[Broken] = Tagged.decoder("broken") {
    case "post"          => _ => Right(Broken.Post)
    case "always"        => _.get[NodeId]("node").map(Broken.Always(_))
    case "assumption"    => _.get[NodeId]("node").map(Broken.Assumption(_))
    case "not-evaluated" => _.get[EvalError]("error").map(Broken.NotEvaluated(_))
    case "threw"         => _.get[String]("message").map(Broken.Threw(_))
  }
