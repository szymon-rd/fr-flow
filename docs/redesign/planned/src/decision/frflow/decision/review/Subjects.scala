package frflow.decision.review

import frflow.core.graph.Walk
import frflow.core.name.NodeId

/** The subjects of a knowledge base, every one after all it rests on: the order decisions are taken in. */
final case class Subjects(inOrder: List[Subject]):
  private lazy val byId: Map[NodeId, Subject] = inOrder.map(s => s.id -> s).toMap
  def get(id: NodeId): Option[Subject] = byId.get(id)
  /** Everything `s` rests on, however far up, nearest first. */
  def ancestry(s: Subject): List[NodeId] =
    Walk.breadthFirst(s.place.restsOn, identity)(get(_).fold(Nil)(_.place.restsOn))
