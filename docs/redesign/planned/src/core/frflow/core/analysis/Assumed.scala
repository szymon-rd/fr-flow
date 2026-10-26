package frflow.core.analysis

/** A piece of behaviour assumed, checked where it can be: an operation's promise the outside keeps, or an outside
  * system (the `index`-th realization of a model) run against its model.
  */
enum Assumed:
  case Promise
  case Outside(index: Int)
