package frflow.core.example

import frflow.core.expr.Value

/** How a flow's run ends: a result, or a failure, each with the world after. */
enum RunEnd:
  case Returns(result: Value, after: Value.World)
  case Fails(error: Value, after: Value.World)
