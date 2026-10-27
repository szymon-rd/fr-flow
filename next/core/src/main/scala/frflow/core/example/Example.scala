package frflow.core.example

import frflow.core.expr.Expr
import frflow.core.spec.Written

/** An example, written as an ordinary test beside the model (owner §18): a closed fact about Definitions applied to
  * values (`granted(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11)) is true`), under values given to the
  * Definitions provided where the code runs. FrFlow checks it against the claims in Lean and against the code in
  * Scala; it shows how things work, and nothing (consistency, vacuity, any rule) depends on it.
  */
final case class Example(name: String, givens: List[Given], fact: Written[Expr])
