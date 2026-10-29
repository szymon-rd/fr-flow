package frflow.testing.report

import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.eval.run.Broken
import frflow.testing.model.{Difference, Step}

/** The smallest failing case found, and where it was drawn: a call that broke what it is tested against, or a run of
  * a model's operations, from a state, that their Scala answered differently from the model.
  */
enum Failure:
  case Call(inputs: List[Value], givens: List[Given], broke: Broken, from: Drawn)
  case Run(start: Value, steps: List[Step], difference: Difference, from: Drawn)

  def from: Drawn
