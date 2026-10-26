package frflow.decision.rules

import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** Re-binding every accepted, unmoved node to its content in `Format.V2` and its code by tokens, as confirmations: one
  * signed decision of the developer's per node, after which no decision is compared on a retired field or raw text.
  */
final class Rebinding(r: Reading, by: Authorship, reason: String):
  def all: Either[Refusal, Ledger] =
    val unmoved = r.subjects.inOrder.filter(s => r.state(s.id) == ReviewState.Accepted)
    if unmoved.isEmpty then Left(Refusal.NothingToConfirm)
    else Right(unmoved.foldLeft(r.ledger)((l, s) =>
      l.add(s.id, Decision.taken(Action.Confirm, by, Reason(reason, Nil), r.bound(s)))))
