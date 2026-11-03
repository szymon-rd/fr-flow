package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.name.NodeId

/** Where an implementation and its model part, as data: a call they did differently (an answer, an error, or one
  * failing alone), a call of an operation known only by assumptions breaking what they say (G2: what it did, and the
  * assumptions broken, none when it threw, which nothing assumed of it covers), such a call made again on the
  * implementation made holding the state before it, giving or leaving another than the first (in Lean the operation
  * is a function of its model's state and its inputs: what each gave, and the state each left), the state the
  * implementation is read back holding after the run when it is not the model's, two calls made at once on the
  * implementation, what it gave each and the state it then held, which neither order of them on the model gives
  * (`CallsAtOnce`), or the implementation not made or not read back (its message).
  */
enum Difference:
  case Call(step: Step, implementation: Ran, model: Ran)
  case Assumed(step: Step, implementation: Ran, broken: List[NodeId])
  case Twice(step: Step, implementation: List[Ran], states: List[Value])
  case State(implementation: Value, model: Value)
  case AtOnce(steps: List[Step], implementation: List[Ran], state: Value)
  case NotRun(message: String)
