package frflow.agent
package conversation

import frflow.ledger.{Idea, IdeaDecision}
import frflow.protocol.*

/** IDEA.md against the conversation it was written from: its `From:` lines name the questions a section comes from. */
object IdeaSources:
  /** The questions each section (by heading; "" for the lead) names on its `From:` lines. */
  def of(idea: String): List[(String, List[String])] =
    val (lead, sections) = Idea.sections(idea)
    def named(text: String) =
      text.linesIterator.collect { case IdeaDecision.FromLine(ids) => ids.split("[,\\s]+").toList.filter(_.nonEmpty) }.flatten.toList
    (("" -> named(lead)) :: sections.map((h, body) => h -> named(body))).filter(_._2.nonEmpty)

  /** What the conversation says of IDEA.md: a section naming a question there is not, and the sections whose answers
    * changed after IDEA.md was accepted (they need a look, and then IDEA.md is accepted again).
    */
  def warnings(idea: String, talk: Conversation, accepted: Option[Decision]): List[String] =
    val srcs = of(idea)
    def where(h: String) = if h.isEmpty then "the lead of IDEA.md" else s"the section \"$h\" of IDEA.md"
    val unknown = srcs.flatMap((h, ids) =>
      ids.filter(talk.question(_).isEmpty).map(q => s"${where(h)} comes from $q, which the conversation does not have"))
    val changed = accepted.toList.flatMap(d => srcs.flatMap((h, ids) =>
      ids.flatMap(talk.question).filter(q => q.replies.size > 1 && q.answeredAt.exists(_.isAfter(d.at)))
        .map(q => s"the answer to ${q.id} changed after IDEA.md was accepted: look again at ${where(h)}, which comes from it")))
    unknown ++ changed.distinct
