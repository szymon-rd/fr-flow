package frflow.agent
package conversation

import frflow.agent.conversation.Defaults.given
import io.circe.derivation.ConfiguredCodec

/** The conversation IDEA.md comes from, as the agent recorded it (`.frflow/conversation.json`). A record, not decisions:
  * the agent writes it and cannot sign as the developer. What the developer decides is IDEA.md, written from it.
  */
final case class Conversation(said: List[Said] = Nil, questions: List[Question] = Nil) derives ConfiguredCodec:
  def question(id: String): Option[Question] = questions.find(_.id.equalsIgnoreCase(id))
  def unanswered: List[Question] = questions.filterNot(_.answered)

object Conversation:
  val empty: Conversation = Conversation()
