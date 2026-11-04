package frflow.eval.run

import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.EvalError

/** What the code says of an example's fact: it holds, it does not, it could not be evaluated, the fact mentions
  * Declarations, which have no code (it is checked against the claims only), or the code threw while it was
  * evaluated (its message: a fault of the code or of its wiring), or a value it writes breaks a rule.
  */
enum OnCode:
  case Holds, Fails
  case NotEvaluated(error: EvalError)
  case Abstract(declarations: List[SymbolName])
  case Threw(message: String)
  /** A value the example writes breaks the rule `always[T]` of its type: no code is given such a value. */
  case BreaksRule(rule: NodeId)
