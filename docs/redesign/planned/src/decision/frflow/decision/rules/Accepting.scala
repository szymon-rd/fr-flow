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
      _ <- ids.traverse_(id => r.subjects.get(id).traverse_(s => unmoved(s, seen.get(id))))
      l <- ids.foldLeftM(r.ledger)((l, id) => one(Reading(r.subjects, l), id, revisit).leftMap(within(ids, id)))
    yield l

  def mechanical: Either[Refusal, Ledger] =
    val batch = r.subjects.inOrder.map(_.id).filter(id => r.notMechanical.get(id).exists(_.isEmpty))
    if batch.isEmpty then Left(Refusal.NothingToConfirm) else nodes(batch, Nil, Map.empty)

  private def one(now: Reading, id: NodeId, revisit: List[NodeId]): Either[Refusal, Ledger] =
    for
      s <- now.subjects.get(id).toRight(Refusal.UnknownNode(id))
      _ <- now.waitsFor(s).map(Refusal.AcceptFirst(_)).toLeft(())
      _ <- Either.cond(now.state(id) != ReviewState.Accepted, (), Refusal.AlreadyAccepted(id))
    yield Below(now, by, reason).settle(s, revisit, chosen(now, s))

  private def chosen(now: Reading, s: Subject): Ledger =
    val rivals = s.place.rivals.filter(x => now.state(x) != ReviewState.Rejected)
    val action = if now.state(s.id) == ReviewState.Review && rivals.isEmpty then Action.Confirm else Action.Accept
    val chosen = now.ledger.add(s.id, Decision.taken(action, by, Reason(reason, rivals), now.bound(s)))
    rivals.flatMap(now.subjects.get).foldLeft(chosen)((l, x) => l.add(x.id, Decision.taken(Action.Reject, by,
      Reason(s"${s.id.value} was chosen instead: $reason", Nil), now.bound(x))))

  private def unmoved(s: Subject, seen: Option[String]) =
    Either.cond(seen.forall(_ == r.version(s)), (), Refusal.MovedSinceSeen(s.id))
  private def within(ids: List[NodeId], id: NodeId)(e: Refusal) =
    if ids.distinct.size > 1 then Refusal.Within(id, e) else e
