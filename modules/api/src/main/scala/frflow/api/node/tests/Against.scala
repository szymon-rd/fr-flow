package frflow.api.node.tests

import frflow.core.name.{ModelName, NodeId, SymbolName}

/** What code was tested against: a claim (or an assumption's formula), or a model (the Scala of its `operations`,
  * reported under `node`).
  */
enum Against:
  case Claim(node: NodeId)
  case Model(node: NodeId, model: ModelName, operations: List[SymbolName])
