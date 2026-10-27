package frflow.testing.model

import frflow.core.name.{BoundaryName, OpName}
import frflow.eval.ScalaValue

/** One call of a generated run of a boundary's operations. */
final case class Step(boundary: BoundaryName, op: OpName, args: List[ScalaValue])
