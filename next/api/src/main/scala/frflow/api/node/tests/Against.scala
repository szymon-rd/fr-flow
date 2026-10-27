package frflow.api.node.tests

import frflow.core.name.NodeId

/** What code was tested against: a claim (or an assumption's formula), or a store's model (one of its realizations). */
enum Against:
  case Claim(node: NodeId)
  case Model(node: NodeId, realization: Int)
