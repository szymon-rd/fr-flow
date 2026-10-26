package frflow.dsl.term

import scala.quoted.*

/** The derivation of a domain type's `LeanType` from its `Mirror`, at compile time: its `DataType`, its `DataRep`, and
  * a compile error when the type (or a supertype) declares its own `equals` or `hashCode`.
  */
object DataMacros:
  def derived[T: Type](using Quotes): Expr[LeanType[T]] = ???
