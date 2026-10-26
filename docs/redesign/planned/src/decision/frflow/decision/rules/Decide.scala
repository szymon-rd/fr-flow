package frflow.decision.rules

import frflow.core.name.NodeId
import frflow.decision.ledger.{Authorship, Decision, Ledger, Reason}
import frflow.decision.review.Reading

/** The one way to record a decision (docs/DAG.md §5): the new ledger, or why it is refused. One rule per command,
  * each over a `Reading` (the subjects with their standings, read once); a reason of a word or two is refused first.
  */
object Decide:
  def apply(r: Reading, c: Command, by: Authorship): Either[Refusal, Ledger] =
    Either.cond(Reason.enough(c.reason), (), Refusal.NoReason).flatMap(_ => rule(r, c, by))

  private def rule(r: Reading, c: Command, by: Authorship): Either[Refusal, Ledger] = c match
    case Command.Accept(ids, why, revisit, seen) => Accepting(r, by, why).nodes(ids, revisit, seen)
    case Command.Reject(id, why, seen)           => Rejecting(r, by, why).node(id, seen)
    case Command.Confirm(why)                    => Accepting(r, by, why).mechanical
    case Command.Revisit(id, why)                => Revisiting(r, by, why).node(id)
    case Command.Gone(id, why)                   => Removing(r, by, why).node(id)
    case Command.Rebind(why)                     => Rebinding(r, by, why).all

  /** The decisions `after` has that `before` did not, subjects parents first, then gone nodes: what the shell signs
    * and reports.
    */
  def added(r: Reading, before: Ledger, after: Ledger): List[(NodeId, Decision)] =
    val subjects = r.subjects.inOrder.map(_.id)
    val others = after.decisions.keys.toList.filterNot(subjects.contains).sortBy(_.value)
    (subjects ++ others).flatMap(id => after.history(id).drop(before.history(id).size).map(id -> _))
