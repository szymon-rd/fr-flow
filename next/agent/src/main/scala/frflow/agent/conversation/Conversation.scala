package frflow.agent.conversation

import io.circe.Codec

/** The conversation a project starts from, as the agent recorded it (`.frflow/conversation.json`): what the developer
  * said and the agent's questions. A record, not decisions: the agent writes it and cannot sign as the developer; what
  * the developer decides are the nodes proposed from it, each in its own decision, with its own reason.
  */
final case class Conversation(said: List[Said], questions: List[Question]) derives Codec.AsObject:
  def question(id: String): Option[Question] = questions.find(_.id.equalsIgnoreCase(id))
  def unanswered: List[Question] = questions.filterNot(_.answered)

object Conversation:
  val empty: Conversation = Conversation(Nil, Nil)
