package frflow.core.code

import frflow.core.expr.Value
import frflow.core.name.{DefName, ModelName, SymbolName}

/** What gives a Definition its meaning (owner §15): proven code (a define, or a program whose run on the models is
  * the vocabulary's `RunOf` define), plain Scala tested by properties, the model of the state it is an operation on
  * (its plain Scala, if given, tested against the model, `CodeTable.implemented`), a value fixed in the model, or a
  * value provided where the code runs (bound by examples, drawn by tests, passed in production).
  */
enum Code:
  case Proven(define: DefName)
  case ProvenFlow(flow: DefName)
  case Tested(runs: ScalaCode, calls: List[SymbolName])
  case Modelled(model: ModelName)
  case Valued(value: Value)
  case Provided

  /** The define Lean proves, if any. */
  def proven: Option[DefName] = this match
    case Proven(d)     => Some(d)
    case ProvenFlow(f) => Some(f)
    case _             => None

  /** The Scala code it runs, if any. */
  def scala: Option[ScalaCode] = this match
    case Tested(r, _) => Some(r)
    case _            => None
