package frflow.decision.review

import frflow.core.name.NodeId
import frflow.decision.content.Chain
import frflow.decision.ledger.{Action, Decision, Ledger}

/** The review states: a fold of the ledger over the subjects, parents first (a parent rejected moves its parts). */
final class Standings(subjects: Subjects, ledger: Ledger):
  lazy val all: Map[NodeId, Standing] =
    val chains = Chains.of(subjects)
    subjects.inOrder.foldLeft(Map.empty[NodeId, Standing])((done, s) =>
      done.updated(s.id, standing(s, Chains.above(s, chains), done)))

  private def standing(s: Subject, above: Chain, done: Map[NodeId, Standing]): Standing =
    val causes = ledger.binding(s.id).fold(Nil)(d => causesOf(s, d, above, done) ++
      List(Cause.Revisit -> ledger.current(s.id).exists(_.action == Action.Revisit),
        Cause.Merged -> ledger.forked(s.id)).collect { case (c, true) => c })
    Standing(state(ledger.current(s.id), s, causes), causes)

  private def causesOf(s: Subject, d: Decision, above: Chain, done: Map[NodeId, Standing]): List[Cause] =
    val (was, now) = (d.bound.content, s.content)
    val moved = was.hash != now.hash
    val added = now.texts("writers").filterNot(was.texts("writers").contains)
    List(
      Cause.Self  -> (moved && Meaning.own(was).hash != Meaning.own(now).hash),
      Cause.Above -> (aboveMoved(s, d, above) || parentRejected(s, done)),
      Cause.Parts -> (moved && was.texts("parts").toSet != now.texts("parts").toSet),
      Cause.Code  -> !sameCode(d, s),
      Cause.Writers(added) -> added.nonEmpty
    ).collect { case (c, true) => c }

  private def aboveMoved(s: Subject, d: Decision, above: Chain): Boolean =
    d.bound.chain != above && !Reworded.only(subjects, ledger, s, d)

  private def sameCode(d: Decision, s: Subject): Boolean = (d.bound.code, s.code) match
    case (None, None)           => true
    case (Some(was), Some(now)) => now.matches(was)
    case _                      => false

  private def parentRejected(s: Subject, done: Map[NodeId, Standing]): Boolean =
    s.place.parents.exists(p => done.get(p).exists(_.state == ReviewState.Rejected))

  private def state(current: Option[Decision], s: Subject, causes: List[Cause]): ReviewState = current match
    case Some(d) if d.action == Action.Reject =>
      if d.bound.content.hash == s.content.hash then ReviewState.Rejected else ReviewState.Proposed
    case Some(d) if d.action.binds || d.action == Action.Revisit =>
      if causes.nonEmpty then ReviewState.Review else ReviewState.Accepted
    case _ => ReviewState.Proposed
