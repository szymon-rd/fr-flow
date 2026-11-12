package frflow.eval

import frflow.core.name.{DefName, SymbolName}

/** Why a term has no Scala value: it quantifies over a type, it reads a symbol nothing binds, it calls a define the
  * vocabulary lacks, or its match has no arm for the value's case.
  */
enum EvalError:
  case Quantified
  case Unbound(symbol: SymbolName)
  case NoDefine(define: DefName)
  case NoCase
