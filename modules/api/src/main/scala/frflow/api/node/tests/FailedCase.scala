package frflow.api.node.tests

import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.eval.run.Broken

/** The smallest failing case, and where it was drawn: a call that broke what it is tested against (its inputs, the
  * values given it).
  */
final case class FailedCase(inputs: List[Value], givens: List[Given], broke: Broken, from: Drawn)
