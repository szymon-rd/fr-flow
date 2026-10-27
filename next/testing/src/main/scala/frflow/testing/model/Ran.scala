package frflow.testing.model

import frflow.core.expr.Value

/** What one call did, as data: gave its result, failed with an error of the program's (the boundary's declared
  * error, typed), or threw something else (its message: an adapter's failure no error of the boundary's covers).
  */
enum Ran:
  case Gave(result: Value)
  case Failed(error: Value)
  case Threw(message: String)
