package frflow.eval.run

import frflow.core.name.SymbolName
import frflow.eval.EvalError

/** What the code says of an example's fact: it holds, it does not, it could not be evaluated, or the fact mentions
  * Declarations, which have no code (it is checked against the claims only).
  */
enum OnCode:
  case Holds, Fails
  case NotEvaluated(error: EvalError)
  case Abstract(declarations: List[SymbolName])
