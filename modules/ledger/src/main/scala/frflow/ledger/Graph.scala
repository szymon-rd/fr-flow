package frflow
package ledger

import frflow.protocol.*
import scala.annotation.tailrec

/** The shape of a snapshot, apart from any decision: what each node rests on, what rests on it, the
  * order decisions are taken in, the alternatives, and each node's chain.
  */
final class Graph(val snapshot: Snapshot):
  val nodes: List[SnapNode] = snapshot.nodes
  val byId: Map[NodeId, SnapNode] = nodes.map(n => n.id -> n).toMap
  val children: Map[NodeId, List[SnapNode]] = nodes.flatMap(n => n.parents.map(_ -> n)).groupMap(_._1)(_._2)

  /** What rests on each node: its parts, the nodes that use it (a definition), the nodes whose code
    * calls it (a contract), and the contracts that keep it (an invariant). A change of its meaning
    * shows on each, as `above`.
    */
  val dependents: Map[NodeId, List[SnapNode]] =
    nodes.flatMap(n => (n.parents ++ n.uses ++ n.relies ++ n.invariants.map(_.id)).distinct.map(_ -> n)).groupMap(_._1)(_._2)

  def dependentsOf(id: NodeId): List[SnapNode] = dependents.getOrElse(id, Nil)

  /** What a node rests on: its parents, the definitions it uses, the contracts its code calls. */
  def restsOn(n: SnapNode): List[NodeId] = (n.parents ++ n.uses ++ n.relies).distinct.filter(byId.contains)

  /** Every node after all it rests on: the order decisions are taken in, a batch's too. */
  lazy val order: List[NodeId] = Graph.topological(nodes.map(_.id), id => byId.get(id).fold(Nil)(restsOn))
  lazy val rank: Map[NodeId, Int] = order.zipWithIndex.toMap

  /** Everything `n` rests on, however far up. */
  def ancestry(n: SnapNode): Set[NodeId] = Graph.closure(restsOn(n), id => byId.get(id).fold(Nil)(restsOn))

  /** `n`'s ancestors through its parents only, nearest first (each once). */
  def ancestors(n: SnapNode): List[SnapNode] =
    Graph.preorder(n.parents, id => byId.get(id).fold(Nil)(_.parents)).flatMap(byId.get)

  /** The nodes of the model that are alternatives to each (see `Graph.alternatives`). */
  lazy val rivals: Map[NodeId, List[NodeId]] =
    val byTerm = nodes.flatMap(n => n.defines.map(_ -> n)).groupMap(_._1)(_._2)
    val replacing = nodes.flatMap(n => n.replaces.flatMap(byId.get).toList.flatMap(r => List(n -> r, r -> n)))
    (replacing ++ nodes.flatMap(n => n.defines.flatMap(byTerm.getOrElse(_, Nil)).map(n -> _)))
      .filter((a, b) => a.id != b.id && Graph.alternatives(a, b))
      .groupMap(_._1.id)(_._2.id).view.mapValues(_.distinct.sortBy(x => rank.getOrElse(x, 0))).toMap

  /** Each node's chain: its meaning, with what it rests on (one pass, parents first). */
  lazy val chains: Map[NodeId, Chain] = chainsOver(order)

  /** What a node rests on, as decided: the chains of its parents, of the definitions it uses and of the
    * contracts its code calls. A design decision rests on its parents' place, not their meaning: a change
    * above lists it below, to revisit.
    */
  def parentChain(n: SnapNode): Chain = parentChainFrom(n, chains)

  /** As `parentChain`, computing only the chains of what `n` rests on. */
  def parentChainAlone(n: SnapNode): Chain =
    val up = ancestry(n)
    parentChainFrom(n, chainsOver(order.filter(up)))

  private def chainsOver(ids: List[NodeId]): Map[NodeId, Chain] =
    ids.flatMap(byId.get).foldLeft(Map.empty[NodeId, Chain])((done, n) =>
      done.updated(n.id, Meaning.chain(n.content, parentChainFrom(n, done))))

  private def parentChainFrom(n: SnapNode, chains: Map[NodeId, Chain]): Chain =
    if n.kind == NodeKind.Design then Chain.empty
    else Meaning.above(Chain.empty, restsOn(n).map(chains.getOrElse(_, Chain.empty)))

object Graph:
  def apply(snapshot: Snapshot): Graph = new Graph(snapshot)

  /** Whether two nodes are alternatives to each other: one replaces the other, or both define one term.
    * Parts under one parent are not: together they make it.
    */
  def alternatives(a: SnapNode, b: SnapNode): Boolean =
    a.replaces.contains(b.id) || b.replaces.contains(a.id) || a.defines.intersect(b.defines).nonEmpty

  private final case class Visited(order: Vector[NodeId], seen: Set[NodeId]):
    def add(id: NodeId): Visited = Visited(order :+ id, seen + id)

  /** Each id after its dependencies (depth first, in the order given; a cycle is cut where it closes). */
  def topological(ids: List[NodeId], deps: NodeId => List[NodeId]): List[NodeId] =
    def visit(done: Visited, id: NodeId, path: Set[NodeId]): Visited =
      if done.seen(id) || path(id) then done
      else deps(id).foldLeft(done)(visit(_, _, path + id)).add(id)
    ids.foldLeft(Visited(Vector.empty, Set.empty))(visit(_, _, Set.empty)).order.toList

  /** The ids reached from `from` through `next`, each once, depth first and nearest first. */
  def preorder(from: List[NodeId], next: NodeId => List[NodeId]): List[NodeId] =
    def visit(done: Visited, id: NodeId): Visited =
      if done.seen(id) then done else next(id).foldLeft(done.add(id))(visit)
    from.foldLeft(Visited(Vector.empty, Set.empty))(visit).order.toList

  /** The ids reached from `from` through `next`. */
  def closure(from: List[NodeId], next: NodeId => List[NodeId]): Set[NodeId] =
    @tailrec def go(frontier: List[NodeId], seen: Set[NodeId]): Set[NodeId] = frontier match
      case Nil => seen
      case id :: rest => if seen(id) then go(rest, seen) else go(next(id) ++ rest, seen + id)
    go(from, Set.empty)
