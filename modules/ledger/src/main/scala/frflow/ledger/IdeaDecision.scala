package frflow
package ledger

import frflow.protocol.*
import io.circe.Json

/** IDEA.md as a decision: the developer accepts it (signed), and a change to it brings it back. The root is decided after
  * it; a node naming a section carries that section, so an edit to the section brings the node back too (`Meaning.own`).
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

  /** `From:` lines in IDEA.md say where a section comes from (a meeting, a document, a conversation). Provenance, not
    * meaning: they move no node.
    */
  val FromLine = """(?i)^\s*From:\s*(.*)$""".r
  def withoutSources(idea: String): String = idea.linesIterator.filterNot(FromLine.matches).mkString("\n")
