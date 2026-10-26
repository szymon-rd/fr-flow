package frflow.testing

import frflow.eval.ScalaValue

/** Where an implementation and its model part: a call they answered differently, or the state the implementation is
  * read back holding after the run, when it is not the model's.
  */
enum Difference:
  case Answer(step: Step, implementation: ScalaValue, model: ScalaValue)
  case State(implementation: ScalaValue, model: ScalaValue)
