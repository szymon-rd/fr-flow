package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.name.NodeId

/** Where an implementation and its model part, as data: a call they did differently (an answer, an error, or one
  * failing alone), a call of an operation known only by assumptions breaking what they say (G2: what it did, and the
  * assumptions broken, none when it threw, which nothing assumed of it covers), the state the implementation is read
  * back holding after the run when it is not the model's, or the implementation not made or not read back (its
  * message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case Assumed(step: Step, implementation: Ran, broken: List[NodeId])
  case State(implementation: Value, model: Value)
  case NotRun(message: String)
