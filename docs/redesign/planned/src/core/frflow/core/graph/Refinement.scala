package frflow.core.graph

import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}

/** The DAG: a node's parents are the wholes it is a part of and the invariants it keeps; its parts are the stated
  * nodes below it, in the model's order. `analysis.Validate` makes it acyclic with one root.
  */
final class Refinement(val nodes: List[Node], val edges: List[Edge]):
  private val byId: Map[NodeId, Node] = nodes.map(n => n.id -> n).toMap
  private val up: Map[NodeId, List[NodeId]] = edges.collect {
    case Edge.PartOf(p, w)    => p -> w
    case Edge.Keeps(c, i, _)  => c -> i
  }.groupMap(_._1)(_._2).view.mapValues(_.distinct).toMap
  private val down: Map[NodeId, List[NodeId]] =
    nodes.flatMap(n => parents(n.id).map(_ -> n.id)).groupMap(_._1)(_._2)

  def node(id: NodeId): Option[Node] = byId.get(id)
  def parents(id: NodeId): List[NodeId] = up.getOrElse(id, Nil)
  /** Its parts and the design decisions below it, in the model's order. */
  def children(id: NodeId): List[NodeId] = down.getOrElse(id, Nil)
  /** Its parts: the children Lean states. */
  def parts(id: NodeId): List[NodeId] = children(id).filter(c => byId.get(c).exists(_.statement.stated))
  /** The claims and invariants without parents: exactly one, the root, in a valid theory. */
  def roots: List[Node] = nodes.filter(n => isClaim(n) && parents(n.id).isEmpty)
  /** Nearest first. */
  def ancestors(id: NodeId): List[NodeId] = Walk.breadthFirst(parents(id), identity)(parents)
  /** The leaves below a node, itself if it is one: what its `holds` takes as hypotheses. */
  def leaves(id: NodeId): List[NodeId] =
    parts(id) match
      case Nil => List(id)
      case ps  => ps.flatMap(leaves).distinct

  private def isClaim(n: Node) = n.statement.kind == NodeKind.Claim || n.statement.kind == NodeKind.Invariant

