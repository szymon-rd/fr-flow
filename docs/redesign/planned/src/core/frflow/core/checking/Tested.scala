package frflow.core.checking

/** A piece of code tested, not proven: plain Scala against the statements mentioning its Definition, or the
  * project's own implementation of a boundary (the `index`-th realization of the model) against the model.
  */
enum Tested:
  case Plain
  case Own(index: Int)
