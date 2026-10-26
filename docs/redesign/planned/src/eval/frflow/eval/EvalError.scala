package frflow.eval

import frflow.core.name.{DefName, SymbolName}

/** Why an expression has no Scala value: it quantifies, it reads a symbol nothing binds, it calls a define the
  * vocabulary lacks.
  */
enum EvalError:
  case Quantified
  case Unbound(symbol: SymbolName)
  case NoDefine(define: DefName)
