package frflow.core.example

import frflow.core.expr.Value
import frflow.core.name.SymbolName

/** A value an example gives a Definition provided where the code runs (`grants`), as data. */
final case class Given(symbol: SymbolName, value: Value)
