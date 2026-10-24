package frflow.agent

import frflow.protocol.{NodeId, Version, Words, word}
import io.circe.{Codec, Decoder, Encoder}
import io.circe.derivation.{Configuration, ConfiguredCodec}
import java.time.Instant

private given Configuration = Configuration.default.withDefaults

/** What the developer told the agent in chat, word for word. */
final case class Said(text: String, at: Instant) derives Codec.AsObject

/** The developer's reply to a question, as they said it in chat. */
final case class Reply(text: String, at: Instant) derives Codec.AsObject

/** A question the agent asked, with the answer it assumed; `replies`, the developer's, the last one standing. */
final case class Question(id: String, text: String, assumed: String, at: Instant, replies: List[Reply] = Nil)
    derives ConfiguredCodec:
  def answered: Boolean = replies.nonEmpty
  def answer: Option[String] = replies.lastOption.map(_.text)
  def answeredAt: Option[Instant] = replies.lastOption.map(_.at)

/** The conversation IDEA.md comes from, as the agent recorded it (`.frflow/conversation.json`). A record, not decisions:
  * the agent writes it and cannot sign as the developer. What the developer decides is IDEA.md, written from it.
  */
final case class Conversation(said: List[Said] = Nil, questions: List[Question] = Nil) derives ConfiguredCodec:
  def question(id: String): Option[Question] = questions.find(_.id.equalsIgnoreCase(id))
  def unanswered: List[Question] = questions.filterNot(_.answered)

object Conversation:
  val empty: Conversation = Conversation()

/** A request's id: `R` and the time it was asked, in base 36. */
opaque type RequestId = String
object RequestId:
  def apply(s: String): RequestId = s
  extension (r: RequestId) def value: String = r
  given Codec[RequestId] = Codec.from(Decoder.decodeString, Encoder.encodeString)

enum RequestStatus:
  case Open, Answered, Closed
  override def toString: String = word(productPrefix)
object RequestStatus extends Words[RequestStatus]

/** A request of the developer's to the agent, on a node or on the idea (`.frflow/requests.json`); the node is with the
  * agent until it is answered (`answeredAt`) or the node changes from the `version` it was `seen` at.
  */
final case class Request(id: RequestId, node: Option[NodeId], text: String, by: String, at: Instant,
    status: RequestStatus, answer: Option[String] = None, seen: Option[Version] = None, answeredAt: Option[Instant] = None)
    derives Codec.AsObject
