package frflow.eval.run

import frflow.core.name.NodeId
import frflow.eval.EvalError

/** What a call broke: the post, the cheaper check, an invariant the contract keeps, an assumption about the values it
  * ran with; or its check could not be evaluated, or the code threw (the developer's exception's message).
  */
enum Broken:
  case Post, Check
  case Invariant(id: NodeId)
  case Assumption(id: NodeId)
  case NotEvaluated(error: EvalError)
  case Threw(message: String)
