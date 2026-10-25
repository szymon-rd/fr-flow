package frflow.agent
package queue

import frflow.agent.request.Request
import frflow.protocol.*

object Tasks:
  /** A revisit is the agent's until it answers on the node (`answer NODE`), or changes it. */
  def of(a: Annotated, requests: List[Request]): List[ForAgent] =
    def last(r: Reviewed, action: Action) = r.review.history.reverse.find(_.action == action)
    def answeredSince(r: Reviewed, d: Decision) = requests.exists(q => q.node.contains(r.id) && q.answeredAt.exists(!_.isBefore(d.at)))
    val rejected = a.nodes.filter(_.state == ReviewState.Rejected)
      .flatMap(r => last(r, Action.Reject).map(d => ForAgent.Replace(r.id, d.by, d.reason)))
    val revisits = a.nodes.filter(_.review.causes.contains(Cause.Revisit))
      .flatMap(r => last(r, Action.Revisit).filterNot(answeredSince(r, _)).map(d => ForAgent.Revisit(r.id, d.reason)))
    val moves = a.nodes.map(r => r -> frflow.ledger.Waiting.rejectedParents(a, r)).collect { case (r, ps) if ps.nonEmpty => ForAgent.Move(r.id, ps) }
    rejected ++ revisits ++ moves
