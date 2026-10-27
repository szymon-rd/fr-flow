package frflow.testing.report

/** Where a part is in a formula's term: its place among the parts built at its level, under each binder above it
  * (the binder's own place first); in a model test, an operation's place in the boundary and a branch's in its steps.
  */
final case class Position(path: List[Int])
