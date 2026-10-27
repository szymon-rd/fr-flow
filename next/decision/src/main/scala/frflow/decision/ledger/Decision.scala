package frflow.decision.ledger

/** One decision of the developer about a node. `after` names the decision it follows (two following one: a merge
  * kept both branches).
  */
final case class Decision(action: Action, author: Authorship, reason: Reason, bound: Bound, after: Option[EntryRef],
    seal: Option[Seal])

object Decision:
  /** A decision as a rule takes it: not yet added (`Ledger.add` sets `after`), not yet signed. */
  def taken(action: Action, author: Authorship, reason: Reason, bound: Bound): Decision =
    Decision(action, author, reason, bound, None, None)
