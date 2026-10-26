package frflow.runtime

import frflow.core.name.{BoundaryName, NodeId, SymbolName}

/** Why a service cannot be wired. */
enum WiringError:
  case NotAContract(node: NodeId)
  case NoCode(contract: NodeId)
  case Unbound(contract: NodeId, symbols: List[SymbolName])
  case UnboundBoundary(contract: NodeId, boundary: BoundaryName)
  case AssumptionBroken(assumption: NodeId)
