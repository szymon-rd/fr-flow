package frflow.eval.flow

import frflow.core.name.SymbolName
import frflow.eval.EvalError

/** Why a program's run in Scala stopped short of its steps: raised in `F`, since the run cannot go on. */
enum FlowError extends scala.util.control.NoStackTrace:
  case NotEvaluated(error: EvalError)
  /** A call of an operation nothing gives a meaning there: no model's, or no Scala bound. */
  case NoOperation(op: SymbolName)
