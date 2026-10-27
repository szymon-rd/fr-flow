package frflow.core.ty

/** Which Scala integer a number is. Lean has one unbounded `Int`; Scala's `Int` and `Long` wrap around, so the IR keeps
  * them apart: they compare, but do not add, and nothing may be said to exist of a type that holds one.
  */
enum NumKind:
  case Int32, Int64, Big
  def bounded: Boolean = this != Big
