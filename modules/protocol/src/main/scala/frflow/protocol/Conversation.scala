package frflow.protocol

import io.circe.Codec
import io.circe.derivation.ConfiguredCodec
import java.time.Instant

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

/** The conversation the idea comes from, as the agent recorded it (`.frflow/conversation.json`). A record, not decisions:
  * the agent writes it and cannot sign as the developer. What the developer decides is IDEA.md, written from it.
  */
final case class Conversation(said: List[Said] = Nil, questions: List[Question] = Nil) derives ConfiguredCodec:
  def question(id: String): Option[Question] = questions.find(_.id.equalsIgnoreCase(id))
  def unanswered: List[Question] = questions.filterNot(_.answered)

object Conversation:
  val empty: Conversation = Conversation()

/** IDEA.md as a decision of the developer's, kept in the ledger under `IDEA`: proposed until accepted, under review once
  * it changes from what was accepted. `version` is the text as the developer saw it.
  */
final case class IdeaReview(state: ReviewState, version: Version, binding: Option[Decision], text: String) derives Codec.AsObject

object IdeaReview:
  /** The ledger's entry for IDEA.md: not a node, so no node may be called this. */
  val Id: NodeId = NodeId("IDEA")
