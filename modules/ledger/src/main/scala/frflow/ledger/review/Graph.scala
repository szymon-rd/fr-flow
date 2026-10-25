package frflow
package ledger
package review

import frflow.protocol.*

/** The shape of a snapshot, apart from any decision: what rests on what, the order of decisions, the alternatives, the chains. */
final class Graph(val snapshot: Snapshot):
  val nodes: List[SnapNode] = snapshot.nodes
  val byId: Map[NodeId, SnapNode] = nodes.map(n => n.id -> n).toMap
  val children: Map[NodeId, List[SnapNode]] = nodes.flatMap(n => n.parents.map(_ -> n)).groupMap(_._1)(_._2)
  val dependents: Map[NodeId, List[SnapNode]] =
    nodes.flatMap(n => (n.parents ++ n.uses ++ n.relies ++ n.invariants.map(_.id)).distinct.map(_ -> n)).groupMap(_._1)(_._2)
  def dependentsOf(id: NodeId): List[SnapNode] = dependents.getOrElse(id, Nil)
  def restsOn(n: SnapNode): List[NodeId] = (n.parents ++ n.uses ++ n.relies).distinct.filter(byId.contains)
  /** Every node after all it rests on: the order decisions are taken in, a batch's too. */
  lazy val order: List[NodeId] = Walk.postorder(nodes.map(_.id), identity)(id => byId.get(id).fold(Nil)(restsOn))
  lazy val rank: Map[NodeId, Int] = order.zipWithIndex.toMap
  /** Everything `n` rests on, however far up, nearest first. */
  def ancestry(n: SnapNode): List[NodeId] = Walk.breadthFirst(restsOn(n), identity)(id => byId.get(id).fold(Nil)(restsOn))
  /** Through its parents only, each once. */
  def ancestors(n: SnapNode): List[SnapNode] =
    Walk.preorder(n.parents, identity)(id => byId.get(id).fold(Nil)(_.parents)).flatMap(byId.get)
  lazy val rivals: Map[NodeId, List[NodeId]] =
    val byTerm = nodes.flatMap(n => n.defines.map(_ -> n)).groupMap(_._1)(_._2)
    val replacing = nodes.flatMap(n => n.replaces.flatMap(byId.get).toList.flatMap(r => List(n -> r, r -> n)))
    (replacing ++ nodes.flatMap(n => n.defines.flatMap(byTerm.getOrElse(_, Nil)).map(n -> _)))
      .filter((a, b) => a.id != b.id && Graph.alternatives(a, b))
      .groupMap(_._1.id)(_._2.id).view.mapValues(_.distinct.sortBy(x => rank.getOrElse(x, 0))).toMap
  private lazy val chains: Map[NodeId, Chain] = chainsOver(order)

  /** What a node rests on, as decided; a design decision rests on its parents' place, not their meaning. */
  def parentChain(n: SnapNode): Chain = parentChainFrom(n, chains)

  private def chainsOver(ids: List[NodeId]): Map[NodeId, Chain] =
    ids.flatMap(byId.get).foldLeft(Map.empty[NodeId, Chain])((done, n) =>
      done.updated(n.id, Meaning.chain(n.content, parentChainFrom(n, done))))

  private def parentChainFrom(n: SnapNode, chains: Map[NodeId, Chain]): Chain =
    if n.kind == NodeKind.Design then Chain.empty
    else Meaning.above(Chain.empty, restsOn(n).map(chains.getOrElse(_, Chain.empty)))

object Graph:
  /** One replaces the other, or both define one term. Parts under one parent are not: together they make it. */
  def alternatives(a: SnapNode, b: SnapNode): Boolean =
    a.replaces.contains(b.id) || b.replaces.contains(a.id) || a.defines.intersect(b.defines).nonEmpty
