package frflow.testing.search

import frflow.core.expr.{Expr, Value}

/** A case refuting a step: the claim's inputs, and the answer the part's claim gives on them. */
final case class Refuted(inputs: List[(String, Value)], answer: Expr)
