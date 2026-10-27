package frflow.api.node.tests

import frflow.core.expr.Value

/** What one call did: gave its result, failed with an error of the program's, or threw something else (its message). */
enum Ran:
  case Gave(result: Value)
  case Failed(error: Value)
  case Threw(message: String)
