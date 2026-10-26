package frflow.dsl.build

import frflow.core.name.{DefName, NodeId}

/** Where a part of a model is written: in a node, or in a define (elaborated once, wherever it is called). */
enum Site:
  case Node(id: NodeId)
  case Define(name: DefName)
