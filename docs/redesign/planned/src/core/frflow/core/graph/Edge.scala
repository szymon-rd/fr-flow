package frflow.core.graph

import frflow.core.expr.Lambda
import frflow.core.name.NodeId
import frflow.core.spec.Written

/** A relation the developer declares between two nodes, from the node it is declared on: a part of a whole, an
  * alternative to another, a contract keeping an invariant through a view (it is then a part of it), an exemption.
  */
enum Edge:
  case PartOf(part: NodeId, whole: NodeId)
  case Replaces(alternative: NodeId, original: NodeId)
  case Keeps(contract: NodeId, invariant: NodeId, view: Written[Lambda])
  case Exempt(node: NodeId, invariant: NodeId, because: String)

  /** The node the edge is declared on. */
  def from: NodeId = this match
    case PartOf(p, _)      => p
    case Replaces(a, _)    => a
    case Keeps(c, _, _)    => c
    case Exempt(n, _, _)   => n
