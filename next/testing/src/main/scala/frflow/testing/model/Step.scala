package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.name.SymbolName

/** One call of a generated run of a model's operations: the operation's Definition, and its arguments as data, typed
  * by its parameters.
  */
final case class Step(op: SymbolName, args: List[Value])
