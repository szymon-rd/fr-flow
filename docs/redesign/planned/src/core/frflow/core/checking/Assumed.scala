package frflow.core.checking

/** A piece of behaviour assumed, checked where it can be: an outside system's promise about a Definition with code
  * (its adapter tested against it), or an outside system (the `index`-th realization of a model) run against its
  * model.
  */
enum Assumed:
  case Assumption
  case Outside(index: Int)
