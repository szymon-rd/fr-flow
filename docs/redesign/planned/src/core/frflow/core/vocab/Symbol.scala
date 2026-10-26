package frflow.core.vocab

import frflow.core.name.SymbolName

/** A value named before its meaning is known, as a statement mentions it: a Declaration or a Definition. */
final case class Symbol(name: SymbolName, means: String, ty: SymbolType, kind: ValueKind)
