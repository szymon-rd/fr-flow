package frflow.dsl.build

import frflow.core.name.{DefName, ModelName, NodeId, SymbolName}

/** Where a part of a model is written: in a node, in a define (elaborated once, wherever it is called), in what the
  * FrModel gives a Definition, in a model of a state's body, or in an example.
  */
enum Site:
  case Node(id: NodeId)
  case Define(name: DefName)
  case Meaning(of: SymbolName)
  case Model(name: ModelName)
  case Example(name: String)
