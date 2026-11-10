package frflow.api.view.source

import frflow.core.name.{DefName, ModelName}
import frflow.core.expr.Value

/** What gives a Definition its meaning, with the text it is given by, as written: a define Lean proves the code of, a
  * proven program, plain Scala tested against what is stated of it, a value fixed, the code it runs in, or a model
  * (with its operations' Scala, when they are tested against it).
  */
enum MeantBy:
  case Proven(define: DefName, written: String)
  case ProvenProgram(program: DefName, written: String)
  case Tested(scala: String)
  case Valued(value: Value)
  case Provided
  case Modelled(model: ModelName, scala: Option[String])
