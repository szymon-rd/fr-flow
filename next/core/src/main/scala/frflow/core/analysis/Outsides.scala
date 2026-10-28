package frflow.core.analysis

import frflow.core.expr.{Exprs, OutsideFact}
import frflow.core.graph.Edge
import frflow.core.name.{BoundaryName, NodeId}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.Theory

/** The assumptions about the world outside the code (owner §16, §21), by what each says: a fact about the outside,
  * or what values of a type from outside meet (an assumption of `always[T]`).
  */
object Outsides:
  def all(t: Theory): List[(NodeId, OutsideFact)] =
    t.nodes.map(_.node).flatMap(n => n.statement.outside.map(n.id -> _))

  /** The assumptions that a store behaves as its model. */
  def modelled(t: Theory, b: BoundaryName): List[NodeId] = all(t).collect {
    case (id, OutsideFact.BehavesAs(`b`, _)) => id
  }

  /** Whether what a boundary gives back is said: by a model it behaves as, or by an assumption mentioning its
    * operations (an outside system's promise). That runs on it are atomic says nothing of what it gives.
    */
  def checks(t: Theory, b: BoundaryName): Boolean = modelled(t, b).nonEmpty || t.nodes.map(_.node).exists(n =>
    n.statement.kind == NodeKind.Assumption && n.statement.outside.isEmpty &&
      n.statement.exprs.exists(e => Exprs.mentions(e).boundaries.contains(b)))

  /** The assumptions of `always[T]` on `ty`: what values of it from outside meet. */
  def alwaysOf(t: Theory, ty: Ty): List[NodeId] = t.nodes.map(_.node).filter(assumesAlways(_, ty)).map(_.id)

  /** The assumption saying `premise`, if there is one. */
  def saying(t: Theory, premise: Premise): Option[NodeId] =
    t.nodes.map(_.node).find(saysOf(_, premise)).map(_.id)

  /** The premises a node's `.assuming` lists that say `premise`. */
  def assumed(t: Theory, node: NodeId, premise: Premise): Option[NodeId] =
    premises(t, node).find(p => t.node(p).exists(saysOf(_, premise)))

  /** Whether a node says something about the outside: a fact, or what values of a type from outside meet. */
  def aboutOutside(n: Node): Boolean = n.statement.outside.nonEmpty || n.statement.range.exists {
    case Range.Made(ty) => assumesAlways(n, ty)
    case _              => false
  }

  /** Whether node `n` says `p`. */
  def saysOf(n: Node, p: Premise): Boolean = p match
    case Premise.FromOutside(ty) => assumesAlways(n, ty)
    case _                       => n.statement.outside.exists(says(_, p))

  private def assumesAlways(n: Node, ty: Ty): Boolean =
    n.statement.kind == NodeKind.Assumption && n.statement.range.contains(Range.Made(ty))

  /** What a node's `.assuming` lists. */
  def premises(t: Theory, node: NodeId): List[NodeId] = t.edges.collect { case Edge.Assumes(`node`, p) => p }

  def says(f: OutsideFact, p: Premise): Boolean = (f, p) match
    case (OutsideFact.BehavesAs(_, m), Premise.BehavesAs(n))         => m == n
    case (OutsideFact.Atomic(b), Premise.Atomic(c))                  => b == c
    case (OutsideFact.Initially(m, _), Premise.Initially(n))         => m == n
    case _                                                           => false
