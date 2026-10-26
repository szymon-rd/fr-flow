package frflow.core.name

/** The name of an open term of the vocabulary (`grants`, `admit`): a parameter or an operation. */
opaque type SymbolName = String

object SymbolName extends Label[SymbolName]
