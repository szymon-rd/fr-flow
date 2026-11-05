package frflow.core.expr

/** Which side of an outcome (`Except E A`): the error, or the value. */
enum Side:
  case Error, Value
