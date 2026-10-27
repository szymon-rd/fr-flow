package frflow.core.analysis

import frflow.core.expr.OutsideFact
import frflow.core.graph.Edge
import frflow.core.name.{BoundaryName, ModelName, NodeId, SymbolName}
import frflow.core.Theory

/** The assumptions about the world outside the code (owner §16), by what each says. */
object Outsides:
  def all(t: Theory): List[(NodeId, OutsideFact)] =
    t.nodes.map(_.node).flatMap(n => n.statement.outside.map(n.id -> _))

  /** The assumptions that a store behaves as its model. */
  def modelled(t: Theory, b: BoundaryName): List[NodeId] = all(t).collect {
    case (id, OutsideFact.BehavesAs(`b`, _)) => id
  }

  /** The programs the outside lets write a model's state. */
  def writers(t: Theory, m: ModelName): List[SymbolName] = all(t).collect {
    case (_, OutsideFact.WrittenOnlyBy(`m`, ps)) => ps
  }.flatten

  /** The assumption saying `fact` of `premise`'s subject, if there is one. */
  def saying(t: Theory, premise: Premise): Option[NodeId] = all(t).collectFirst {
    case (id, f) if says(f, premise) => id
  }

  /** The premises a node's `.assuming` lists that say `premise`. */
  def assumed(t: Theory, node: NodeId, premise: Premise): Option[NodeId] =
    premises(t, node).find(p => t.node(p).exists(_.statement.outside.exists(says(_, premise))))

  /** What a node's `.assuming` lists. */
  def premises(t: Theory, node: NodeId): List[NodeId] = t.edges.collect { case Edge.Assumes(`node`, p) => p }

  def says(f: OutsideFact, p: Premise): Boolean = (f, p) match
    case (OutsideFact.BehavesAs(_, m), Premise.BehavesAs(n))         => m == n
    case (OutsideFact.OneRunAtATime(m), Premise.OneRunAtATime(n))    => m == n
    case (OutsideFact.Initially(m, _), Premise.Initially(n))         => m == n
    case (OutsideFact.WrittenOnlyBy(m, _), Premise.WrittenOnlyBy(n)) => m == n
    case (OutsideFact.Calls(d), Premise.Calls(e))                    => d == e
    case _                                                           => false
