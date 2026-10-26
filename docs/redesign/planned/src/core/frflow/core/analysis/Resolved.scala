package frflow.core.analysis

import frflow.core.name.{NodeId, SymbolName}
import frflow.core.Theory

/** A valid theory with, per node, what its proven code calls and relies on. */
final class Resolved private[analysis] (val theory: Theory, calls: Map[NodeId, List[NodeId]],
    relies: Map[NodeId, List[NodeId]]):
  def callsOf(id: NodeId): List[NodeId] = calls.getOrElse(id, Nil)
  def reliesOn(id: NodeId): List[NodeId] = relies.getOrElse(id, Nil)
  /** What one Definition's proven code relies on: the statements constraining the Definitions it calls. */
  def reliedOnBy(op: SymbolName): List[NodeId] = Resolve.constrainingCalled(theory, Callees.ofDefinition(theory, op))
  /** Its parents, the premises it assumes and the callees it relies on: what its decision rests on. */
  def restsOn(id: NodeId): List[NodeId] =
    (theory.refinement.parents(id) ++ theory.refinement.assumed(id) ++ reliesOn(id)).distinct
