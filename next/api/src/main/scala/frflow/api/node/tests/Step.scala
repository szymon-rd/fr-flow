package frflow.api.node.tests

import frflow.core.expr.Value
import frflow.core.name.SymbolName

/** One call of a generated run of a model's operations, with its arguments. */
final case class Step(op: SymbolName, args: List[Value])
