package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** Asking that a decided node be reviewed again: a change elsewhere may affect it. */
final class Revisiting(r: Reading, by: Authorship, reason: String):
  def node(id: NodeId): Either[Refusal, Ledger] =
    for
      s <- r.subjects.get(id).toRight(Refusal.UnknownNode(id))
      _ <- Either.cond(r.ledger.binding(id).isDefined, (), Refusal.NotDecided(id))
      _ <- Either.cond(!r.ledger.current(id).exists(_.action == Action.Revisit), (), Refusal.AlreadyRevisited(id))
    yield r.ledger.add(id, Decision.taken(Action.Revisit, by, Reason(reason, Nil), r.bound(s)))
