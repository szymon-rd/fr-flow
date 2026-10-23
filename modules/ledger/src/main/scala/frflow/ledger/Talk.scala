package frflow
package ledger

import frflow.protocol.*
import io.circe.Json
import java.time.Instant

/** IDEA.md as a decision: the agent writes it from the conversation, the developer accepts it (signed), and a change to it
  * brings it back. The root is decided after it; a node naming a section carries that section, so an edit to the section
  * brings the node back too (`Meaning.own`).
  */
object IdeaDecision:
  val Id: NodeId = IdeaReview.Id
  def content(idea: String): Content = Content("idea" -> Json.fromString(idea))
  def version(idea: String): Version = Version(content(idea).hash.value.take(16))

  /** None while there is no IDEA.md. */
  def review(snapshot: Snapshot, ledger: Ledger): Option[IdeaReview] =
    Option.when(snapshot.idea.trim.nonEmpty) {
      val binding = ledger.binding(Id)
      val now = content(snapshot.idea).hash
      val state = binding.fold(ReviewState.Proposed)(d => if d.hash == now then ReviewState.Accepted else ReviewState.Review)
      IdeaReview(state, version(snapshot.idea), binding, snapshot.idea)
    }

  /** Accepting IDEA.md as it is now, unless it moved since `seen`. */
  def accept(snapshot: Snapshot, ledger: Ledger, reason: String, seen: Option[Version], by: String, stamp: Stamp): Either[Refusal, Ledger] =
    review(snapshot, ledger) match
      case None => Left(Refusal.NoIdea)
      case Some(r) if seen.exists(_ != r.version) => Left(Refusal.MovedSinceSeen(Id))
      case Some(r) if r.state == ReviewState.Accepted => Left(Refusal.AlreadyAccepted(Id))
      case Some(_) =>
        Right(ledger.add(Id, Decision(Action.Accept, by, stamp.at, reason, commit = stamp.commit, content = content(snapshot.idea))))

  /** The `From:` lines of IDEA.md: which answers a section comes from. Provenance, not meaning: they move no node. */
  private val FromLine = """(?i)^\s*From:\s*(.*)$""".r
  def withoutSources(idea: String): String = idea.linesIterator.filterNot(FromLine.matches).mkString("\n")

  /** The questions each section (by heading; "" for the lead) names on its `From:` lines. */
  def sources(idea: String): List[(String, List[String])] =
    val (lead, sections) = Idea.sections(idea)
    def named(text: String) =
      text.linesIterator.collect { case FromLine(ids) => ids.split("[,\\s]+").toList.filter(_.nonEmpty) }.flatten.toList
    (("" -> named(lead)) :: sections.map((h, body) => h -> named(body))).filter(_._2.nonEmpty)

  /** What the conversation says of IDEA.md now: a section naming a question there is not, and the sections whose answers
    * changed after IDEA.md was accepted (they need a look, and then IDEA.md is accepted again).
    */
  def warnings(idea: String, talk: Conversation, accepted: Option[Decision]): List[String] =
    val srcs = sources(idea)
    def where(h: String) = if h.isEmpty then "the lead of IDEA.md" else s"the section \"$h\" of IDEA.md"
    val unknown = srcs.flatMap((h, ids) =>
      ids.filter(talk.question(_).isEmpty).map(q => s"${where(h)} comes from $q, which the conversation does not have"))
    val changed = accepted.toList.flatMap(d => srcs.flatMap((h, ids) =>
      ids.flatMap(talk.question).filter(q => q.replies.size > 1 && q.answeredAt.exists(_.isAfter(d.at)))
        .map(q => s"the answer to ${q.id} changed after IDEA.md was accepted: look again at ${where(h)}, which comes from it")))
    unknown ++ changed.distinct

/** The conversation as the agent records it. Pure: each returns the new record, or why not. */
object Talk:
  def say(c: Conversation, text: String, now: Instant): Either[Refusal, (Conversation, Said)] =
    nonEmpty(text).map { t =>
      val s = Said(t, now)
      (c.copy(said = c.said :+ s), s)
    }

  /** A question with the answer the agent assumed: numbered Q1, Q2, … in the order asked. */
  def ask(c: Conversation, text: String, assumed: String, now: Instant): Either[Refusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      a <- nonEmpty(assumed).left.map(_ => Refusal.NoAssumption)
    yield
      val q = Question(s"Q${c.questions.size + 1}", t, a, now)
      (c.copy(questions = c.questions :+ q), q)

  /** The developer's reply, as said in chat: a later one stands (the earlier ones are kept). */
  def reply(c: Conversation, id: String, text: String, now: Instant): Either[Refusal, (Conversation, Question)] =
    for
      t <- nonEmpty(text)
      q <- c.question(id).toRight(Refusal.UnknownQuestion(id))
    yield
      val answered = q.copy(replies = q.replies :+ Reply(t, now))
      (c.copy(questions = c.questions.map(x => if x.id == q.id then answered else x)), answered)

  private def nonEmpty(text: String): Either[Refusal, String] = Option(text.trim).filter(_.nonEmpty).toRight(Refusal.NoText)
