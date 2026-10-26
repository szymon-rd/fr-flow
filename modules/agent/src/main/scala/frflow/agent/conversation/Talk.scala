package frflow.agent
package conversation

import java.time.Instant

/** The conversation as the agent records it: each operation returns the new record, or why not. */
object Talk:
  def say(c: Conversation, text: String, now: Instant): Either[AgentRefusal, (Conversation, Said)] =
    nonEmpty(text).map { t =>
      val s = Said(t, now)
      (c.copy(said = c.said :+ s), s)
    }

  /** A question with the answer the agent assumed: numbered Q1, Q2, … in the order asked. */
  def ask(c: Conversation, text: String, assumed: String, now: Instant): Either[AgentRefusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      a <- nonEmpty(assumed).left.map(_ => AgentRefusal.NoAssumption)
    yield
      val q = Question(s"Q${c.questions.size + 1}", t, a, now)
      (c.copy(questions = c.questions :+ q), q)

  /** The developer's reply, as said in chat: a later one stands (the earlier ones are kept). */
  def reply(c: Conversation, id: String, text: String, now: Instant): Either[AgentRefusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      q <- c.question(id).toRight(AgentRefusal.UnknownQuestion(id))
    yield
      val answered = q.copy(replies = q.replies :+ Reply(t, now))
      (c.copy(questions = c.questions.map(x => if x.id == q.id then answered else x)), answered)

  private def nonEmpty(text: String): Either[AgentRefusal, String] = Option(text.trim).filter(_.nonEmpty).toRight(AgentRefusal.NoText)
