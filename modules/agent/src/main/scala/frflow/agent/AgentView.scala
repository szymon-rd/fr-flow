package frflow.agent

import frflow.agent.conversation.{Conversation, IdeaSources}
import frflow.agent.queue.{ForAgent, Tasks}
import frflow.agent.request.{Request, RequestStatus}
import frflow.api.View
import frflow.protocol.*

/** A view of the project with what the agent layer keeps beside it: the developer's requests and the conversation. */
final case class AgentView(view: View, requests: List[Request], conversation: Conversation):
  /** The developer's open requests on a node they have not seen change since: the node is with the agent. */
  def asked(r: Reviewed): List[Request] =
    requests.filter(q => q.node.contains(r.id) && q.status == RequestStatus.Open && q.seen.forall(_ == r.review.version))
  def withAgent(r: Reviewed): Boolean = asked(r).nonEmpty
  /** The nodes with the agent: held back from the developer's queue until it answers or changes them. */
  def held: Set[NodeId] = view.nodes.filter(withAgent).map(_.id).toSet
  def open: List[Request] = requests.filter(_.status == RequestStatus.Open)
  def answers: List[Request] = requests.filter(_.status == RequestStatus.Answered)
  def forAgent: List[ForAgent] = Tasks.of(view.annotated, requests)
  /** IDEA.md against the conversation: what `status` and `ci` fail on, beside the core's warnings. */
  def warnings: List[String] = IdeaSources.warnings(view.snapshot.idea, conversation, view.annotated.idea.flatMap(_.binding))
