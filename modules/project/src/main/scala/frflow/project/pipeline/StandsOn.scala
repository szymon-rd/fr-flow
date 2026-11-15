package frflow.project.pipeline

import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** What a node stands on at the bottom, through its parts all the way down: the assumptions it is proven from, and
  * the claims (itself among them) that are not proven for a reason of their own: with no part that is itself not
  * proven, so not merely waiting for one. A node with none is proven from its assumptions alone; each one is what
  * its proof still lacks.
  */
final case class StandsOn(assumed: List[NodeId], unproven: List[NodeId])

object StandsOn:
  def of(a: Analysis, id: NodeId): StandsOn =
    val t = a.decided.theory
    val below = Walk.breadthFirst(List(id), identity)(t.refinement.parts).flatMap(t.node)
    val open = below.filter(n => n.statement.kind == NodeKind.Claim && ReadProof.of(a, n).unproven.nonEmpty)
      .map(_.id).toSet
    StandsOn(below.filter(_.statement.kind == NodeKind.Assumption).map(_.id).sortBy(_.value),
      open.filterNot(n => t.refinement.parts(n).exists(open)).toList.sortBy(_.value))

  /** Of each root, by its name. */
  def roots(a: Analysis): Map[NodeId, StandsOn] =
    a.decided.theory.refinement.roots.map(n => n.id -> of(a, n.id)).toMap
