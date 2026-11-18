package frflow.core.graph

import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** What a node stands on at the bottom, through its parts all the way down: the assumptions it is proven from, and
  * the claims (itself among them) that are not proven for a reason of their own: with no part that is itself not
  * proven, so not merely waiting for one. A node with none is proven from its assumptions alone; each one is what
  * its proof still lacks.
  */
final case class StandsOn(assumed: List[NodeId], unproven: List[NodeId])

object StandsOn:
  /** Over any reading of the graph: a node's parts, its kind (none of what is no node), and whether a claim is not
    * proven.
    */
  def over(parts: NodeId => List[NodeId], kind: NodeId => Option[NodeKind], open: NodeId => Boolean)(id: NodeId)
      : StandsOn =
    val below = Walk.breadthFirst(List(id), identity[NodeId])(parts).filter(kind(_).isDefined)
    val unproven = below.filter(n => kind(n).contains(NodeKind.Claim) && open(n)).toSet
    StandsOn(below.filter(kind(_).contains(NodeKind.Assumption)).sortBy(_.value),
      unproven.filterNot(n => parts(n).exists(unproven)).toList.sortBy(_.value))
