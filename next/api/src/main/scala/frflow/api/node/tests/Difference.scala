package frflow.api.node.tests

import frflow.core.expr.Value
import frflow.core.name.NodeId

/** Where an implementation and its model part: a call they did differently, a call of an operation known only by
  * assumptions breaking what they say (none broken when it threw), the state the implementation is read back holding
  * when it is not the model's, or the implementation not made or not read back (its message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case Assumed(step: Step, implementation: Ran, broken: List[NodeId])
  case State(implementation: Value, model: Value)
  case NotRun(message: String)
