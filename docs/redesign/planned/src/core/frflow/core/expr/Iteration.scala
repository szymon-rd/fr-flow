package frflow.core.expr

/** An operation with a body over the elements of a list or an option, the receiver's type telling which:
  * `xs.forall(p)`, `o.exists(p)`, `xs.filter(p)`, `xs.map(f)`.
  */
enum Iteration:
  case Forall, Exists, Filter, FilterNot, Find, Map, FlatMap
