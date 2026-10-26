package frflow.dsl.node

import frflow.core.name.SymbolName

/** A parameter's value for an example or a running service: code evaluated on use, or a table (`bindTable`). */
enum Binding:
  case Value(symbol: SymbolName, value: () => Any)
  case Table(symbol: SymbolName, entries: Map[?, ?])
