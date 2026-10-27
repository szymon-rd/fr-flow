package frflow.decision.review

import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** Where a node sits, as decisions read it: its parents, everything it rests on (parents, premises it assumes,
  * callees it relies on), its alternatives, and its kind.
  */
final case class Place(parents: List[NodeId], restsOn: List[NodeId], rivals: List[NodeId], kind: NodeKind):
  /** A design rests on its parents' place only. */
  def design: Boolean = kind == NodeKind.Design
  /** A design holds a choice Lean does not check (a fixed term is a `define`, decided with the statements using it). */
  def holdsChoice: Boolean = design
