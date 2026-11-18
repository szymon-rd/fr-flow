package frflow.api.view.vocab

import frflow.api.view.source.MeantBy
import frflow.core.name.SymbolName
import frflow.core.vocab.{SymbolType, ValueKind}

/** A Declaration or a Definition: what it means, its type, and what gives it its meaning (none for a Declaration,
  * and for a Definition nothing gives one yet).
  */
final case class Word(name: SymbolName, means: String, kind: ValueKind, ty: SymbolType, meant: Option[MeantBy])
