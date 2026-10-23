package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** What is the agent's to do: a rejected node to replace with what the reason asks for (or remove), a
  * node the developer asked to revisit, a node resting on a rejected one to move.
  */
enum ForAgent derives Codec.AsObject:
  case Replace(node: NodeId, by: String, reason: String)
  case Revisit(node: NodeId, reason: String)
  case Move(node: NodeId, rejectedParents: List[NodeId])

/** Who waits on whom. */
object Waiting:
  def forAgent(a: Annotated): List[ForAgent] =
    def last(r: Reviewed, action: Action) = r.review.history.reverse.find(_.action == action)
    val rejected = a.nodes.filter(_.state == ReviewState.Rejected)
      .flatMap(r => last(r, Action.Reject).map(d => ForAgent.Replace(r.id, d.by, d.reason)))
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit))
      .map(r => ForAgent.Revisit(r.id, last(r, Action.Revisit).fold("")(_.reason)))
    val moves = a.nodes.map(r => r -> rejectedParents(a, r)).collect { case (r, ps) if ps.nonEmpty => ForAgent.Move(r.id, ps) }
    rejected ++ revisits ++ moves

  /** The parents of a node that were rejected: it waits for the agent to move it. */
  def rejectedParents(a: Annotated, r: Reviewed): List[NodeId] =
    r.node.parents.filter(p => a.byId.get(p).exists(_.state == ReviewState.Rejected))

  /** The nodes waiting for a developer's decision, in the order to take them: proposed or under review, and not
    * resting on a rejected node (that one waits for the agent to move it).
    */
  def forDeveloper(a: Annotated): List[Reviewed] =
    val rank = a.order.zipWithIndex.toMap
    a.nodes.filter(r => (r.state == ReviewState.Proposed || r.state == ReviewState.Review) && rejectedParents(a, r).isEmpty)
      .sortBy(r => rank.getOrElse(r.id, Int.MaxValue))
