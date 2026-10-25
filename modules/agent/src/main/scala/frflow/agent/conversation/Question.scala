package frflow.agent
package conversation

import frflow.agent.conversation.Defaults.given
import io.circe.derivation.ConfiguredCodec
import java.time.Instant

/** A question the agent asked, with the answer it assumed; `replies`, the developer's, the last one standing. */
final case class Question(id: String, text: String, assumed: String, at: Instant, replies: List[Reply] = Nil)
    derives ConfiguredCodec:
  def answered: Boolean = replies.nonEmpty
  def answer: Option[String] = replies.lastOption.map(_.text)
  def answeredAt: Option[Instant] = replies.lastOption.map(_.at)
