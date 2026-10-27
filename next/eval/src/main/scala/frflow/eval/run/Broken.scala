package frflow.eval.run

import frflow.core.name.NodeId
import frflow.eval.EvalError

/** What a call broke in a generated test: the post, an `always[T]` of a value it was given or made, an assumption
  * about the values it ran with; or the post could not be evaluated, or the code threw (its exception's message).
  */
enum Broken:
  case Post
  case Always(id: NodeId)
  case Assumption(id: NodeId)
  case NotEvaluated(error: EvalError)
  case Threw(message: String)
