package frflow.agent.conversation

import cats.syntax.all.*
import frflow.agent.request.AgentRefusal
import java.time.Instant

/** The conversation as the agent records it: each operation returns the new record and what it added, or why not. */
object Talk:
  def say(c: Conversation, text: String, now: Instant): Either[AgentRefusal, (Conversation, Said)] =
    words(text).map(t => Said(t, now)).map(s => (c.copy(said = c.said :+ s), s))

  /** A question with the answer the agent assumed, its id the time it was asked in base 36 (`q…`, the next free one
    * when two are asked at once).
    */
  def ask(c: Conversation, text: String, assumed: String, now: Instant)
      : Either[AgentRefusal, (Conversation, Question)] =
    (words(text), words(assumed).leftMap(_ => AgentRefusal.NoAssumption)).mapN { (t, a) =>
      val taken = c.questions.map(_.id).toSet
      val id = Iterator.from(0).map(i => s"q${java.lang.Long.toString(now.toEpochMilli + i, 36)}").dropWhile(taken)
        .next()
      val q = Question(id, t, a, now, Nil)
      (c.copy(questions = c.questions :+ q), q)
    }

  /** The developer's reply, as said in chat: a later one stands (the earlier ones are kept). */
  def reply(c: Conversation, id: String, text: String, now: Instant): Either[AgentRefusal, (Conversation, Question)] =
    (words(text), c.question(id).toRight(AgentRefusal.UnknownQuestion(id))).mapN { (t, q) =>
      val answered = q.copy(replies = q.replies :+ Said(t, now))
      (c.copy(questions = c.questions.map(x => if x.id == q.id then answered else x)), answered)
    }

  private def words(text: String): Either[AgentRefusal, String] =
    Option(text.trim).filter(_.nonEmpty).toRight(AgentRefusal.NoText)
