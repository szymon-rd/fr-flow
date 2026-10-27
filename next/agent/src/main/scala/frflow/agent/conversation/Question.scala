package frflow.agent.conversation

import io.circe.Codec
import java.time.Instant

/** A question the agent asked in chat, with the answer it assumed (so the developer can just agree), and the
  * developer's replies, the last one standing. Its id names it in `replied`, by the time it was asked: no question
  * is numbered, and nothing outside the conversation refers to one (owner §1).
  */
final case class Question(id: String, text: String, assumed: String, at: Instant, replies: List[Said])
    derives Codec.AsObject:
  def answer: Option[String] = replies.lastOption.map(_.text)
  def answered: Boolean = replies.nonEmpty
