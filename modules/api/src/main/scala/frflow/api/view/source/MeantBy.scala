package frflow.api.view.source

import frflow.core.name.DefName
import frflow.core.expr.Value

/** What gives a Definition its meaning, with the text it is given by, as written: a define Rocq proves the code of,
  * plain Scala tested against what is stated of it, a value fixed, the code it runs in, or compiled classes whose
  * executions are read (by the classes' names).
  */
enum MeantBy:
  case Proven(define: DefName, written: String)
  case Tested(scala: String)
  case Valued(value: Value)
  case Provided
  case Executed(units: List[String])
