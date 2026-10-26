package frflow.core.example

import frflow.core.code.Impl
import frflow.core.expr.Value

/** The value an example gives a symbol: data (Lean evaluates the example with it), a lookup table (`bindTable`:
  * Lean evaluates lookups in it), or Scala code (the example runs in Scala only).
  */
enum Supply:
  case Data(value: Value)
  case Table(entries: List[(Value, Value)])
  case Code(impl: Impl)

  /** Data or a table: built as a literal of the symbol's type. */
  def literal: Boolean = this match
    case Code(_) => false
    case _       => true
