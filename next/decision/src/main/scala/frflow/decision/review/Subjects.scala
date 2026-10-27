package frflow.decision.review

import frflow.core.graph.Walk
import frflow.core.name.NodeId

/** The subjects of a knowledge base, every one after all it rests on: the order decisions are taken in. */
final case class Subjects(inOrder: List[Subject]):
  private lazy val byId: Map[NodeId, Subject] = inOrder.map(s => s.id -> s).toMap
  def get(id: NodeId): Option[Subject] = byId.get(id)
  private lazy val resting: Map[NodeId, List[Subject]] =
    inOrder.flatMap(s => s.place.restsOn.distinct.map(_ -> s)).groupMap(_._1)(_._2)
  private lazy val children: Map[NodeId, List[Subject]] =
    inOrder.flatMap(s => s.place.parents.distinct.map(_ -> s)).groupMap(_._1)(_._2)
  private lazy val rank: Map[NodeId, Int] = inOrder.map(_.id).zipWithIndex.toMap
  /** The subjects resting on `id` directly, in order. */
  def restingOn(id: NodeId): List[Subject] = resting.getOrElse(id, Nil)
  /** Its parts: the subjects with `id` among their parents, in order. */
  def childrenOf(id: NodeId): List[Subject] = children.getOrElse(id, Nil)
  /** The ids, each once, in the order decisions are taken; those not in the model last, as given. */
  def ordered(ids: List[NodeId]): List[NodeId] = ids.distinct.sortBy(rank.getOrElse(_, Int.MaxValue))
  /** Everything `s` rests on, however far up, nearest first. */
  def ancestry(s: Subject): List[NodeId] =
    Walk.breadthFirst(s.place.restsOn, identity)(get(_).fold(Nil)(_.place.restsOn))
