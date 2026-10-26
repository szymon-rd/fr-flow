package frflow.core.vocab

import frflow.core.name.SymbolName

/** An open term of the domain: a fact of the world or an operation of the system. */
final case class Symbol(name: SymbolName, means: String, ty: SymbolType)
