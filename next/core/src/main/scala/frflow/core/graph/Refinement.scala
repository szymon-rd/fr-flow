package frflow.core.graph

import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}

/** The DAG: a node's parents are the wholes it is below; its parts are the stated nodes below it, in the model's
  * order, but its rules (the statements of `always` below it). A premise a node assumes (`Edge.Assumes`) is beside
  * the order, never a part. `analysis.Validate` makes it acyclic, with at least one root.
  */
final class Refinement(val nodes: List[Node], val edges: List[Edge]):
  private val byId: Map[NodeId, Node] = nodes.map(n => n.id -> n).toMap
  private val up: Map[NodeId, List[NodeId]] =
    edges.collect { case Edge.PartOf(p, w) => p -> w }.groupMap(_._1)(_._2).view.mapValues(_.distinct).toMap
  private val down: Map[NodeId, List[NodeId]] =
    nodes.flatMap(n => parents(n.id).map(_ -> n.id)).groupMap(_._1)(_._2)

  def node(id: NodeId): Option[Node] = byId.get(id)
  def parents(id: NodeId): List[NodeId] = up.getOrElse(id, Nil)
  /** Its parts and the design decisions below it, in the model's order. */
  def children(id: NodeId): List[NodeId] = down.getOrElse(id, Nil)
  /** Its parts: the children Lean states, but its rules. Its parts together, with the assumptions it lists, imply
    * it; that step is proven (`complete`, `impl`), each part needed.
    */
  def parts(id: NodeId): List[NodeId] =
    children(id).filter(c => byId.get(c).exists(n => n.statement.stated && !n.statement.rule))
  /** Its rules: the statements of `always` placed below it (`.refines`). Each is a hypothesis Lean has of every value
    * of its type or store already, proven by its own obligations, so it is no part of the step (2.4).
    */
  def rules(id: NodeId): List[NodeId] = children(id).filter(c => byId.get(c).exists(_.statement.rule))
  /** The premises `id` assumes, in the order written. */
  def assumed(id: NodeId): List[NodeId] = edges.collect { case Edge.Assumes(`id`, p) => p }
  /** The root statements: the claims without parents, on any Definitions and Declarations, a claim relating several
    * (owner §11: a small set; keeping it concise is the author's job). A service's purpose is often a claim about its
    * entry flow. An assumption is trusted, so it is no root.
    */
  def roots: List[Node] = nodes.filter(n => rootKind(n) && parents(n.id).isEmpty)
  /** Nearest first. */
  def ancestors(id: NodeId): List[NodeId] = Walk.breadthFirst(parents(id), identity)(parents)
  /** The leaves below a node, itself if it is one: what its `holds` takes as hypotheses. */
  def leaves(id: NodeId): List[NodeId] =
    parts(id) match
      case Nil => List(id)
      case ps  => ps.flatMap(leaves).distinct

  private def rootKind(n: Node) = n.statement.kind == NodeKind.Claim

