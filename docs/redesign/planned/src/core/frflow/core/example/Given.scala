package frflow.core.example

import frflow.core.name.{SourceText, SymbolName}

/** A symbol's value under which an example is run (`grants.bind(List(…))`), with its expression as written. */
final case class Given(symbol: SymbolName, supply: Supply, written: SourceText)
