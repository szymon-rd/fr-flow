package frflow.core.vocab

import frflow.core.ty.Ty

/** A symbol's type, or none: a value only plain code reads (a database connection) has no Lean type, so it cannot
  * appear in a statement (`CodeOnlyInStatement`); what it is in Scala (`scalaType`) is what to give one.
  */
enum SymbolType:
  case Typed(ty: Ty)
  case CodeOnly(scalaType: String)
