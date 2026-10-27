package frflow.eval.run

import frflow.core.name.SymbolName
import frflow.eval.EvalError

/** What the code says of an example's fact: it holds, it does not, it could not be evaluated, the fact mentions
  * Declarations, which have no code (it is checked against the claims only), or the code threw while it was
  * evaluated (its message: a fault of the code or of its wiring).
  */
enum OnCode:
  case Holds, Fails
  case NotEvaluated(error: EvalError)
  case Abstract(declarations: List[SymbolName])
  case Threw(message: String)
