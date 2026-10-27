package frflow.testing.report

import frflow.core.name.{DefName, NodeId}

/** What code was tested against: a claim, a define, or a model (its realization). */
enum Against:
  case Claim(node: NodeId)
  case Define(name: DefName)
  case Model(node: NodeId, realization: Int)
