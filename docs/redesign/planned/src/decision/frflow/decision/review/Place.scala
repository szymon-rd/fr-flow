package frflow.decision.review

import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** Where a node sits, as decisions read it: its parents, everything it rests on (parents, definitions it uses,
  * callees it relies on), its alternatives, and its kind.
  */
final case class Place(parents: List[NodeId], restsOn: List[NodeId], rivals: List[NodeId], kind: NodeKind):
  /** A design rests on its parents' place only. */
  def design: Boolean = kind == NodeKind.Design
  /** A design or a definition holds a choice Lean does not check. */
  def holdsChoice: Boolean = design || kind == NodeKind.Definition
