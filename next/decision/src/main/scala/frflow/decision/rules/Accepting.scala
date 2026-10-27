package frflow.decision.rules

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** Accepting nodes, parents first: chosen or confirmed, rivals rejected, what moved only with them confirmed. */
final class Accepting(r: Reading, by: Authorship, reason: String):
  def nodes(ids: List[NodeId], revisit: List[NodeId], seen: Map[NodeId, String]): Either[Refusal, Ledger] =
    for
      _ <- Either.cond(ids.nonEmpty, (), Refusal.NoNodes)
      _ <- notBelow(ids, revisit).map(Refusal.NotBelow(ids.head, _)).toLeft(())
      _ <- ids.traverse_(id => r.subjects.get(id).traverse_(s => unmoved(s, seen.get(id))))
      l <- each(ids, true, (now, s, l) => Below(now, by, reason).settle(s, revisit, l))
    yield l

  /** The mechanical batch, each node accepted on its own, choosing among no rivals: what is below it is in the batch
    * or decided apart.
    */
  def mechanical: Either[Refusal, Ledger] =
    val batch = r.subjects.inOrder.map(_.id).filter(id => r.notMechanical.get(id).exists(_.isEmpty))
    if batch.isEmpty then Left(Refusal.NothingToConfirm) else each(batch, false, (_, _, l) => l)

  /** Each node accepted in order; with `choosing`, over its rivals not yet rejected. */
  private def each(ids: List[NodeId], choosing: Boolean, after: (Reading, Subject, Ledger) => Ledger)
      : Either[Refusal, Ledger] =
    r.subjects.ordered(ids).foldLeftM(r.ledger) { (l, id) =>
      val now = Reading(r.subjects, l)
      one(now, id, choosing).map((s, chosen) => after(now, s, chosen)).leftMap(within(ids, id))
    }

  /** An accepted node is accepted again only over a rival still standing. */
  private def one(now: Reading, id: NodeId, choosing: Boolean): Either[Refusal, (Subject, Ledger)] =
    for
      s <- now.subjects.get(id).toRight(Refusal.UnknownNode(id))
      _ <- now.waitsFor(s).map(Refusal.AcceptFirst(_)).toLeft(())
      _ <- Option.when(s.proof.unproven.contains(Unproven.Tests))(Refusal.CodeFails(id)).toLeft(())
      _ <- Option.when(s.proof.unproven.contains(Unproven.NotTested))(Refusal.NotTested(id)).toLeft(())
      rivals = if choosing then s.place.rivals.filter(x => now.state(x) != ReviewState.Rejected) else Nil
      _ <- Either.cond(now.state(id) != ReviewState.Accepted || rivals.nonEmpty, (), Refusal.AlreadyAccepted(id))
    yield s -> chosen(now, s, rivals)

  /** A node under review whose meaning did not move is confirmed, keeping the reason it was chosen for. */
  private def chosen(now: Reading, s: Subject, rivals: List[NodeId]): Ledger =
    val meaningMoved =
      now.causes(s.id).contains(Cause.Self) && now.ledger.binding(s.id).forall(Meaning.decisionMoved(_, s))
    val confirms = now.state(s.id) == ReviewState.Review && !meaningMoved && rivals.isEmpty
    val action = if confirms then Action.Confirm else Action.Accept
    val chosen = now.ledger.add(s.id, Decision.taken(action, by, Reason(reason, rivals), now.bound(s)))
    rivals.flatMap(now.subjects.get).foldLeft(chosen)((l, x) => l.add(x.id, Decision.taken(Action.Reject, by,
      Reason(s"${s.id.value} was chosen instead: $reason", Nil), now.bound(x))))

  /** The nodes named to revisit that are not among the decisions below the nodes accepted. */
  private def notBelow(ids: List[NodeId], revisit: List[NodeId]): Option[List[NodeId]] =
    val below = ids.flatMap(r.subjects.get).filter(s => r.state(s.id) != ReviewState.Accepted)
      .flatMap(Below(r, by, reason).actsOn).map(_.id).toSet
    Option(revisit.filterNot(below)).filter(_.nonEmpty)

  private def unmoved(s: Subject, seen: Option[String]) =
    Either.cond(seen.forall(_ == r.version(s)), (), Refusal.MovedSinceSeen(s.id))
  private def within(ids: List[NodeId], id: NodeId)(e: Refusal) =
    if ids.distinct.size > 1 then Refusal.Within(id, e) else e
