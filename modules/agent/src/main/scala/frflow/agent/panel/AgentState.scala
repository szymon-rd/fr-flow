package frflow.agent.panel

import frflow.agent.conversation.{Conversation, Question}
import frflow.agent.request.Request
import frflow.agent.work.{AgentView, ForAgent}
import frflow.core.name.NodeId
import io.circe.derivation.{Configuration, ConfiguredEncoder}
import io.circe.{Encoder, Json}

/** What the web view's agent panels read, in one call: the requests, the conversation and its questions open, the
  * nodes with the agent, and what is the agent's to do.
  */
final case class AgentState(requests: List[Request], conversation: Conversation, questions: List[Question],
    withAgent: List[NodeId], forAgent: List[ForAgent])

object AgentState:
  def of(a: AgentView): AgentState =
    AgentState(a.requests, a.conversation, a.conversation.unanswered, a.held.toList.sorted, a.forAgent)

  private given Configuration = Configuration.default.withDiscriminator("type")
  private given Encoder[NodeId] = Encoder.encodeString.contramap(_.value)
  private given Encoder.AsObject[ForAgent] = ConfiguredEncoder.derived

  given Encoder.AsObject[AgentState] = Encoder.AsObject.instance(s => io.circe.JsonObject(
    "requests" -> Encoder[List[Request]].apply(s.requests),
    "conversation" -> Encoder[Conversation].apply(s.conversation),
    "questions" -> Encoder[List[Question]].apply(s.questions), "withAgent" -> Json.arr(s.withAgent.map(n =>
      Json.fromString(n.value))*), "forAgent" -> Encoder[List[ForAgent]].apply(s.forAgent)))
