package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.ledger.{Action, Authorship, Decision, Ledger, Reason}
import frflow.decision.review.*

/** After a node is accepted: the decisions below it that moved only with it confirmed, each once all it rests on
  * holds, parents first; those named revisited (docs/DAG.md §5). Which decisions it acts on is `Moves`'.
  */
final class Below(r: Reading, by: Authorship, reason: String):
  def settle(s: Subject, revisit: List[NodeId], after: Ledger): Ledger =
    val below = Moves.actsOn(r, s)
    val confirmed = below.filter(c => r.state(c.id) == ReviewState.Review && !revisit.contains(c.id))
      .foldLeft(after)((l, c) =>
        if c.place.restsOn.forall(Reading(r.subjects, l).state(_) == ReviewState.Accepted)
        then l.add(c.id, record(Action.Confirm, c, s"still holds after ${s.id.value} changed: $reason"))
        else l)
    below.filter(c => revisit.contains(c.id)).foldLeft(confirmed)((l, c) =>
      l.add(c.id, record(Action.Revisit, c, s"${s.id.value} changed and may affect it: $reason")))

  private def record(a: Action, c: Subject, why: String) = Decision.taken(a, by, Reason(why, Nil), r.bound(c))
