package frflow.testing

import frflow.core.name.{DefName, NodeId}

/** What code was tested against: a node's promise, the define beside production code, or a model (its realization). */
enum Against:
  case Promise(node: NodeId)
  case Define(name: DefName)
  case Model(node: NodeId, realization: Int)
