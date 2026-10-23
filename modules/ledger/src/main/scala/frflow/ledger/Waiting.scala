package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** A decision waiting for the developer: a node proposed or under review (and whether it is
  * mechanical), or a decided node gone from the model.
  */
enum ForDeveloper derives Codec.AsObject:
  case Decide(node: NodeId, causes: List[Cause], mechanical: Boolean)
  case Gone(node: NodeId)

/** What is the agent's to do: a rejected node to replace with what the reason asks for (or remove), a
  * node the developer asked to revisit, a node resting on a rejected one to move.
  */
enum ForAgent derives Codec.AsObject:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])

/** Who waits on whom. */
final case class Waiting(developer: List[ForDeveloper], agent: List[ForAgent]) derives Codec.AsObject

object Waiting:
  val none: Waiting = Waiting(Nil, Nil)

  def of(a: Annotated): Waiting =
    val developer = forDeveloper(a).map(r => ForDeveloper.Decide(r.id, r.review.causes, r.review.mechanical)) ++
      a.gone.map(g => ForDeveloper.Gone(g.id))
    def last(r: Reviewed, action: Action) = r.review.history.reverse.find(_.action == action)
    val rejected = a.nodes.filter(_.state == ReviewState.Rejected)
      .flatMap(r => last(r, Action.Reject).map(d => ForAgent.Replace(r.id, d.by, d.reason)))
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit))
      .map(r => ForAgent.Revisit(r.id, last(r, Action.Revisit).fold("")(_.reason)))
    val moves = a.nodes.map(r => r -> rejectedParents(a, r)).collect { case (r, ps) if ps.nonEmpty => ForAgent.Move(r.id, ps) }
    Waiting(developer, rejected ++ revisits ++ moves)

  /** The parents of a node that were rejected: it waits for the agent to move it. */
  def rejectedParents(a: Annotated, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => a.byId.get(p).exists(_.state == ReviewState.Rejected))

  /** The nodes waiting for a developer's decision: proposed or under review, and not resting on a
    * rejected node (that one waits for the agent to move it). `Load` and `Queue` count the same.
    */
  def forDeveloper(a: Annotated): List[Reviewed] =
    a.nodes.filter(r => (r.state == ReviewState.Proposed || r.state == ReviewState.Review) && rejectedParents(a, r).isEmpty)

/** What waits for the developer, counted: the mechanical decisions (one batch), the new nodes and the
  * changes to judge, and the gone nodes. The cost of a change in decisions, seen as it happens.
  */
final case class Load(mechanical: Int, fresh: Int, changed: Int, gone: Int) derives Codec.AsObject:
  def total: Int = mechanical + fresh + changed + gone

object Load:
  def of(a: Annotated): Load =
    val ns = Waiting.forDeveloper(a)
    val (fresh, changed) = ns.filterNot(_.review.mechanical).partition(_.state == ReviewState.Proposed)
    Load(ns.count(_.review.mechanical), fresh.size, changed.size, a.gone.size)

/** The order the developer decides in, each after what it rests on (definitions and parents first):
  * what is ready, the mechanical batch, what waits for a decision above it, and the gone nodes.
  */
final case class Queue(ready: List[NodeId], mechanical: List[NodeId], waiting: List[NodeId], gone: List[NodeId])
    derives Codec.AsObject

object Queue:
  def of(a: Annotated): Queue =
    val rank = a.order.zipWithIndex.toMap
    val ns = Waiting.forDeveloper(a).sortBy(r => rank.getOrElse(r.id, Int.MaxValue))
    val (mechanical, judged) = ns.partition(_.review.mechanical)
    val (waiting, ready) = judged.partition(_.review.waitsFor.isDefined)
    Queue(ready.map(_.id), mechanical.map(_.id), waiting.map(_.id), a.gone.map(_.id))
