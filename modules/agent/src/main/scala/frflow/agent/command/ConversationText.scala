package frflow.agent
package command

import frflow.agent.conversation.Conversation
import frflow.cli.*

/** The conversation IDEA.md comes from: what the developer said, then each question with the answer assumed and theirs. */
object ConversationText:
  def lines(c: Conversation, st: Style): List[String] =
    if c.said.isEmpty && c.questions.isEmpty then List("Nothing recorded yet: tell the agent your idea in chat.")
    else
      def under(text: String) = Lines.para(text, st, indent = 4).map("  " + _)
      (Lines.section("What you said", c.said.flatMap(s => Lines.para(s.text, st)), st) ++
        Lines.section("What the agent asked", c.questions.flatMap { q =>
          Lines.para(s"[${q.id}] ${q.text}", st) ++ under(st.dim(s"assumed: ${q.assumed}")) ++
            q.replies.dropRight(1).flatMap(r => under(st.dim(s"earlier: ${r.text}"))) ++
            under(q.answer.fold(st.yellow("no reply yet"))(x => s"${st.cyan("you:")} $x"))
        }, st)).dropWhile(_.isEmpty)
