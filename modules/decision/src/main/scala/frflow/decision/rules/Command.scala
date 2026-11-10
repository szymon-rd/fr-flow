package frflow.decision.rules

import frflow.core.name.NodeId

/** A decision the developer asks for. An acceptance is only that: nothing is added to the model with it. What turns
  * a node away (a rejection, a revisit, agreeing a node is gone) says why, in at least three words: the agent reads
  * it to know what to propose instead. `seen`: each node's version as the developer saw it.
  */
enum Command:
  case Accept(nodes: List[NodeId], revisit: List[NodeId], seen: Map[NodeId, String])
  case Reject(node: NodeId, reason: String, seen: Option[String])
  /** Accept every mechanical decision. */
  case Confirm
  case Revisit(node: NodeId, reason: String)
  case Gone(node: NodeId, reason: String)

  /** Why, where it turns a node away; none for an acceptance. */
  def why: Option[String] = this match
    case Reject(_, why, _)          => Some(why)
    case Revisit(_, why)            => Some(why)
    case Gone(_, why)               => Some(why)
    case Accept(_, _, _) | Confirm  => None
