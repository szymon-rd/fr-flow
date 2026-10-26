package frflow.eval

import frflow.core.name.{DefName, ModelName, SymbolName}

/** Why a term has no Scala value: it quantifies over a type, it reads a symbol nothing binds, it calls a define the
  * vocabulary lacks, its match has no arm for the value's case, it reads a model a world lacks, or it is a program's
  * steps (run by `run.FlowInterpreter`, not evaluated).
  */
enum EvalError:
  case Quantified
  case Unbound(symbol: SymbolName)
  case NoDefine(define: DefName)
  case NoCase
  case NoModel(model: ModelName)
  case Steps
