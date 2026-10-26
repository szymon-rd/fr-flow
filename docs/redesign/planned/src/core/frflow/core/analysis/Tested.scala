package frflow.core.analysis

import frflow.core.name.DefName

/** A piece of code tested, not proven: plain code against its promise, production code against the define beside it,
  * or the project's own implementation of a boundary (the `index`-th realization of the model) against the model.
  */
enum Tested:
  case Plain
  case Beside(define: DefName)
  case Own(index: Int)
