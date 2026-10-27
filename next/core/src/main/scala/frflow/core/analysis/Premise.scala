package frflow.core.analysis

import frflow.core.name.{ModelName, SymbolName}

/** A fact about the outside a check rests on, by what it must say (owner §16, §17). */
enum Premise:
  case BehavesAs(model: ModelName)
  case OneRunAtATime(model: ModelName)
  case Initially(model: ModelName)
  case WrittenOnlyBy(model: ModelName)
  case Calls(definition: SymbolName)
