package frflow.core.vocab

import frflow.core.ty.Ty

/** A symbol's type, or none: a parameter only plain code reads (a database connection) has no Lean type, so it
  * cannot appear in a statement (elaboration refuses one that does).
  */
enum SymbolType:
  case Typed(ty: Ty)
  case CodeOnly
