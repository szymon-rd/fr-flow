package frflow.decision.rules

import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** Rejecting a proposal, and the proposals below it, which rested on it. */
final class Rejecting(r: Reading, by: Authorship, reason: String):
  def node(id: NodeId, seen: Option[String]): Either[Refusal, Ledger] =
    for
      s <- r.subjects.get(id).toRight(Refusal.UnknownNode(id))
      _ <- Either.cond(seen.forall(_ == r.version(s)), (), Refusal.MovedSinceSeen(id))
      _ <- Either.cond(r.state(id) == ReviewState.Proposed, (), Refusal.NotAProposal(id, r.state(id)))
    yield below(id).foldLeft(r.ledger.add(id, record(s, reason)))((l, c) =>
      l.add(c.id, record(c, s"${id.value}, which it rested on, was rejected: $reason")))

  private def below(id: NodeId): List[Subject] =
    def proposed(x: NodeId) = r.children(x).filter(c => r.state(c.id) == ReviewState.Proposed).map(_.id)
    Walk.breadthFirst(proposed(id), identity)(proposed).flatMap(r.subjects.get)

  private def record(s: Subject, why: String) = Decision.taken(Action.Reject, by, Reason(why, Nil), r.bound(s))
