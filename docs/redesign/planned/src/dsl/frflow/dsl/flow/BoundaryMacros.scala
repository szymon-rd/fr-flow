package frflow.dsl.flow

import scala.quoted.*

/** `BoundaryOps[T]` from the trait's declared methods: each method's parameters and result with their `LeanType`s
  * summoned, and a `call` that matches on the operation's name.
  */
object BoundaryMacros:
  def derived[T: Type](using Quotes): Expr[BoundaryOps[T]] = ???
