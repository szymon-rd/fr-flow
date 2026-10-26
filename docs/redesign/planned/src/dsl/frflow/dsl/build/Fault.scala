package frflow.dsl.build

import frflow.core.name.{RelPath, SymbolName}

/** What is wrong with a part of a model, wherever it is found: in a term being built, a constant, a path, a link. */
enum Fault:
  case DeclaredLater
  case NoType(where: String)
  case FunctionEquality
  case NotData(value: String)
  case ValueReadWhileBuilding(symbol: SymbolName)
  case BadPath(path: String, why: RelPath.Invalid)
  case OutsideStep
  case Thrown(message: String)
