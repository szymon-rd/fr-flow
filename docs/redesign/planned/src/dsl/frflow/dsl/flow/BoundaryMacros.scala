package frflow.dsl.flow

import scala.quoted.*

/** `BoundaryOps[B]` from the trait's declared methods: each method's parameters and result with their `LeanType`s
  * summoned, and the three instances, each method one line (a call recorded, a call by name, a call lifted).
  */
object BoundaryMacros:
  def derived[B[_[_], _[_]]: Type](using Quotes): Expr[BoundaryOps[B]] = ???
