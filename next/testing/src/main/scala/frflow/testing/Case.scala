package frflow.testing

import frflow.core.example.Given
import frflow.core.expr.Value

/** One generated case of a call: its inputs, and the values its code is given that wiring does not make (drawn), as
  * data, so a failing case is shown, shrunk and replayed as it is.
  */
final case class Case(inputs: List[Value], givens: List[Given])
