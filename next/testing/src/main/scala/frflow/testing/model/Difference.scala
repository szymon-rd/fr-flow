package frflow.testing.model

import frflow.core.expr.Value

/** Where an implementation and its model part, as data: a call they did differently (an answer, an error, or one
  * failing alone), the state the implementation is read back holding after the run when it is not the model's, or
  * the implementation not made or not read back (its message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case State(implementation: Value, model: Value)
  case NotRun(message: String)
