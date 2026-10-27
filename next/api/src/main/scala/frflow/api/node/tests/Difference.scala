package frflow.api.node.tests

import frflow.core.expr.Value

/** Where an implementation and its model part: a call they did differently, the state the implementation is read
  * back holding when it is not the model's, or the implementation not made or not read back (its message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case State(implementation: Value, model: Value)
  case NotRun(message: String)
