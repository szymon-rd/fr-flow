package frflow.api.view.vocab

import frflow.core.name.{ModelName, SymbolName}

/** A model of a state: what it means, and its operations (those given steps, then those known only by assumptions). */
final case class Model(name: ModelName, means: String, operations: List[SymbolName])
