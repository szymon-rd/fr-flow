package frflow.api.node.tests

import frflow.core.expr.Value
import frflow.core.name.{BoundaryName, OpName}

/** One call of a generated run of a boundary's operations, with its arguments. */
final case class Step(boundary: BoundaryName, op: OpName, args: List[Value])
