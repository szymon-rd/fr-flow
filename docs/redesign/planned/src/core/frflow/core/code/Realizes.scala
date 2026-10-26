package frflow.core.code

/** Whose implementation of a boundary it is: an outside system's (a database; its model stays assumed, the
  * implementation is checked against it) or the project's own (tested against the model).
  */
enum Realizes:
  case Outside, Own
