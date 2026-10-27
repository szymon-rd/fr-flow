package frflow.dsl.build

import frflow.core.name.{DefName, NodeId, SymbolName}

/** Where a part of a model is written: in a node, in a define (elaborated once, wherever it is called), in what the
  * knowledge base gives a Definition, or in an example.
  */
enum Site:
  case Node(id: NodeId)
  case Define(name: DefName)
  case Meaning(of: SymbolName)
  case Example(name: String)
