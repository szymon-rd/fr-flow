package frflow.testing.report

import frflow.core.name.{ModelName, NodeId}

/** What code was tested against: a claim (or an assumption's formula), or a model (its operations' Scala, reported
  * under `node`).
  */
enum Against:
  case Claim(node: NodeId)
  case Model(node: NodeId, model: ModelName)
