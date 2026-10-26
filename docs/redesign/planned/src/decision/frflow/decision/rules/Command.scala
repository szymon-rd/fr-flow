package frflow.decision.rules

import frflow.core.name.NodeId

/** A decision the developer asks for, with its reason. `seen`: each node's version as the developer saw it. */
enum Command:
  case Accept(nodes: List[NodeId], reason: String, revisit: List[NodeId], seen: Map[NodeId, String])
  case Reject(node: NodeId, reason: String, seen: Option[String])
  /** Accept every mechanical decision. */
  case Confirm(reason: String)
  case Revisit(node: NodeId, reason: String)
  case Gone(node: NodeId, reason: String)
  /** Bind every unmoved decision to its content in `Format.V2` and its code by tokens: one signed step. */
  case Rebind(reason: String)

  /** Every command has one. */
  def reason: String
