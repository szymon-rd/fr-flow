package frflow.core.graph

import frflow.core.name.NodeId

/** A relation the developer declares between two nodes, from the node it is declared on: a part of a whole
  * (`.refines`), a premise its proof assumes (`.assuming`: a model, a fact, never a part), an alternative to another
  * (`.replaces`, a decision's link).
  */
enum Edge:
  case PartOf(part: NodeId, whole: NodeId)
  case Assumes(node: NodeId, premise: NodeId)
  case Replaces(alternative: NodeId, original: NodeId)

  /** The node the edge is declared on. */
  def from: NodeId = this match
    case PartOf(p, _)   => p
    case Assumes(n, _)  => n
    case Replaces(a, _) => a
