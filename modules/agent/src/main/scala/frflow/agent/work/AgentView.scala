package frflow.agent.work

import frflow.agent.conversation.Conversation
import frflow.agent.request.{Request, RequestStatus}
import frflow.api.node.{NodeView, Relation}
import frflow.api.view.View
import frflow.core.name.NodeId
import frflow.decision.ledger.Action
import frflow.decision.review.{Cause, ReviewState}

/** A view of the project with what the agent layer keeps beside it: the developer's requests and the conversation. */
final case class AgentView(view: View, requests: List[Request], conversation: Conversation):
  /** The developer's open requests on a node they have not seen move since: the node is with the agent. */
  def asked(n: NodeView): List[Request] = requests.filter(q => q.node.contains(n.id) &&
    q.status == RequestStatus.Open && q.asked.seen.forall(_ == n.review.version))
  def withAgent(n: NodeView): Boolean = asked(n).nonEmpty
  /** The nodes with the agent: held back from the developer's queue until it answers or changes them. */
  def held: Set[NodeId] = view.nodes.filter(withAgent).map(_.id).toSet
  def open: List[Request] = requests.filter(_.status == RequestStatus.Open)
  def answers: List[Request] = requests.filter(_.status == RequestStatus.Answered)

  /** What is the agent's to do: each rejected node to replace, each revisit not answered on its node since, each node
    * resting on a rejected one.
    */
  def forAgent: List[ForAgent] =
    val rejected = view.nodes.filter(_.review.standing.state == ReviewState.Rejected)
    rejected.flatMap(n => n.review.decisions.latest.filter(_.action == Action.Reject)
      .map(d => ForAgent.Replace(n.id, d.author.by, d.reason.text))) ++
      view.nodes.filter(_.review.standing.causes.contains(Cause.Revisit)).flatMap(n =>
        n.review.decisions.latest.filter(d => d.action == Action.Revisit && !answeredSince(n.id, d.author.at))
          .map(d => ForAgent.Revisit(n.id, d.reason.text))) ++
      view.nodes.filterNot(rejected.contains)
        .map(n => n -> n.place(Relation.Parent).filter(p => rejected.exists(_.id == p)))
        .collect { case (n, ps) if ps.nonEmpty => ForAgent.Move(n.id, ps) }

  private def answeredSince(id: NodeId, at: java.time.Instant): Boolean =
    requests.exists(q => q.node.contains(id) && q.answer.exists(a => !a.at.isBefore(at)))
