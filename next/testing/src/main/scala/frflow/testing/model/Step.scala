package frflow.testing.model

import frflow.core.expr.Value
import frflow.core.name.{BoundaryName, OpName}

/** One call of a generated run of a boundary's operations: its arguments as data, typed by the operation's
  * parameters.
  */
final case class Step(boundary: BoundaryName, op: OpName, args: List[Value])
