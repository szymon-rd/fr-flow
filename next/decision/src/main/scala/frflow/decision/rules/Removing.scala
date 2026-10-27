package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Authorship, Ledger, Reason}
import frflow.decision.review.*

/** Agreeing that a decided node is gone from the model: its last binding decision, removed. */
final class Removing(r: Reading, by: Authorship, reason: String):
  def node(id: NodeId): Either[Refusal, Ledger] =
    for
      _    <- Either.cond(r.subjects.get(id).isEmpty, (), Refusal.StillInModel(id))
      _    <- Either.cond(r.gone.contains(id), (), Refusal.UnknownNode(id))
      last <- r.ledger.binding(id).toRight(Refusal.UnknownNode(id))
    yield r.ledger.add(id, last.copy(action = Action.Remove, author = by, reason = Reason(reason, Nil), seal = None))
