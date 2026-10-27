package frflow.api.node.tests

import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.eval.run.Broken

/** The smallest failing case, and where it was drawn: a call that broke what it is tested against (its inputs, the
  * values given it), or a run of a boundary's operations from a state that an implementation answered differently
  * from its model.
  */
enum FailedCase:
  case Call(inputs: List[Value], givens: List[Given], broke: Broken, from: Drawn)
  case Run(start: Value, steps: List[Step], difference: Difference, from: Drawn)
