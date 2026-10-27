package frflow.testing.report

import frflow.core.name.NodeId

/** What code was tested against: a claim (or an assumption's formula), or a model (its realization). */
enum Against:
  case Claim(node: NodeId)
  case Model(node: NodeId, realization: Int)
