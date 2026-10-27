package frflow.testing.model

import frflow.eval.ScalaValue

/** Where an implementation and its model part: a call they answered differently, the state the implementation is
  * read back holding after the run when it is not the model's, or the run failing (its message) where the model's
  * does not.
  */
enum Difference:
  case Answer(step: Step, implementation: ScalaValue, model: ScalaValue)
  case State(implementation: ScalaValue, model: ScalaValue)
  case Threw(message: String)
