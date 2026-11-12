package frflow.testing.report

import frflow.core.example.Given
import frflow.core.expr.Value
import frflow.eval.run.Broken

/** The smallest failing case found, and where it was drawn: a call that broke what it is tested against. */
final case class Failure(inputs: List[Value], givens: List[Given], broke: Broken, from: Drawn)
