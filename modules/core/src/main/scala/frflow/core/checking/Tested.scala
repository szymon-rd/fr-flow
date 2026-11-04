package frflow.core.checking

import frflow.core.name.ModelName

/** A piece of code tested, not proven: plain Scala against the statements mentioning its Definition, or the plain
  * Scala of a model's operations against the model, on generated runs, whoever wrote it (owner §36).
  */
enum Tested:
  case Plain
  case Model(model: ModelName)
