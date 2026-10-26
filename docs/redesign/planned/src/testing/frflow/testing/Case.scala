package frflow.testing

import frflow.core.code.Values
import frflow.core.expr.Value

/** One generated case of a call: its inputs, and the values its code is given (drawn where wiring does not make
  * them).
  */
final case class Case(inputs: List[Value], drawn: Values)
