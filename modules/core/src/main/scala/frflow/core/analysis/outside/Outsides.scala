package frflow.core.analysis.outside

import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.Theory

/** The assumptions about the world outside the code (owner §16, §21): what values of a type from outside meet (an
  * assumption of `always[T]`).
  */
object Outsides:
  /** The assumptions of `always[T]` on `ty`: what values of it from outside meet. */
  def alwaysOf(t: Theory, ty: Ty): List[NodeId] = t.nodes.map(_.node).filter(assumesAlways(_, ty)).map(_.id)

  /** The assumption saying `premise`, if there is one. */
  def saying(t: Theory, premise: Premise): Option[NodeId] =
    t.nodes.map(_.node).find(saysOf(_, premise)).map(_.id)

  /** The premises a node's `.assuming` lists that say `premise`. */
  def assumed(t: Theory, node: NodeId, premise: Premise): Option[NodeId] =
    premises(t, node).find(p => t.node(p).exists(saysOf(_, premise)))

  /** Whether a node says what values of a type from outside meet. */
  def aboutOutside(n: Node): Boolean = n.statement.range.exists {
    case Range.Made(ty) => assumesAlways(n, ty)
    case _              => false
  }

  /** Whether node `n` says `p`. */
  def saysOf(n: Node, p: Premise): Boolean = p match
    case Premise.FromOutside(ty) => assumesAlways(n, ty)

  private def assumesAlways(n: Node, ty: Ty): Boolean =
    n.statement.kind == NodeKind.Assumption && n.statement.range.contains(Range.Made(ty))

  /** What a node's `.assuming` lists. */
  def premises(t: Theory, node: NodeId): List[NodeId] = t.edges.collect { case Edge.Assumes(`node`, p) => p }
