package frflow.core.spec

import frflow.core.expr.Expr

/** A consequence the developer expects of a claim, which Lean proves from it (`expect_i`): "Acme never sees Globex's
  * contact".
  */
final case class Expectation(statement: String, consequence: Written[Expr])
