package frflow.core.name

/** The name of a Declaration or a Definition (`authorized`, `grants`, `granted`). */
opaque type SymbolName = String

object SymbolName extends Label[SymbolName]
