package frflow.agent
package panel

import frflow.agent.conversation.{Conversation, Question}
import frflow.agent.queue.ForAgent
import frflow.agent.request.Request
import frflow.protocol.*
import io.circe.Codec

/** What the web view's agent panels read, in one call. */
final case class AgentState(requests: List[Request], conversation: Conversation, withAgent: List[NodeId], forAgent: List[ForAgent],
    questions: List[Question], warnings: List[String]) derives Codec.AsObject

object AgentState:
  def of(a: AgentView): AgentState =
    AgentState(a.requests, a.conversation, a.held.toList.sorted, a.forAgent, a.conversation.unanswered, a.warnings)
