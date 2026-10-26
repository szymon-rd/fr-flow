package frflow.core.analysis

import frflow.core.name.NodeId
import frflow.core.Theory

/** A valid theory with its definitions in force, and per node what it uses, calls and relies on. */
final class Resolved private[analysis] (val theory: Theory, val inForce: InForce, uses: Map[NodeId, List[NodeId]],
    calls: Map[NodeId, List[NodeId]], relies: Map[NodeId, List[NodeId]]):
  def usesOf(id: NodeId): List[NodeId] = uses.getOrElse(id, Nil)
  def callsOf(id: NodeId): List[NodeId] = calls.getOrElse(id, Nil)
  def reliesOn(id: NodeId): List[NodeId] = relies.getOrElse(id, Nil)
  /** Its parents, the definitions it uses and the callees it relies on: what its decision rests on. */
  def restsOn(id: NodeId): List[NodeId] = (theory.refinement.parents(id) ++ usesOf(id) ++ reliesOn(id)).distinct
