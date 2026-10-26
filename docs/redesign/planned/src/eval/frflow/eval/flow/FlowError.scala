package frflow.eval.flow

import frflow.core.name.{BoundaryName, OpName}
import frflow.eval.EvalError

/** Why a program's run in Scala stopped short of its steps: raised in `F`, since the run cannot go on. */
enum FlowError extends scala.util.control.NoStackTrace:
  case NotEvaluated(error: EvalError)
  case NoModel(boundary: BoundaryName)
  case NoOperation(boundary: BoundaryName, op: OpName)
