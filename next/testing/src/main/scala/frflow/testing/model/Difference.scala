package frflow.testing.model

import frflow.core.expr.Value

/** Where an implementation and its model part, as data: a call they did differently (an answer, an error, or one
  * failing alone), the state the implementation is read back holding after the run when it is not the model's, two
  * calls made at once on the implementation, what it gave each and the state it then held, which neither order of
  * them on the model gives (`CallsAtOnce`), or the implementation not made or not read back (its message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case State(implementation: Value, model: Value)
  case AtOnce(steps: List[Step], implementation: List[Ran], state: Value)
  case NotRun(message: String)
