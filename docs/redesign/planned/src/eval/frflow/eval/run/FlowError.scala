package frflow.eval.run

import frflow.core.name.{BoundaryName, OpName}
import frflow.eval.EvalError

/** Why a flow's run stopped short of its steps: raised in `F`, since the run cannot go on. */
enum FlowError extends scala.util.control.NoStackTrace:
  case NotEvaluated(error: EvalError)
  case NotBound(boundary: BoundaryName)
  case NoOperation(boundary: BoundaryName, op: OpName)
