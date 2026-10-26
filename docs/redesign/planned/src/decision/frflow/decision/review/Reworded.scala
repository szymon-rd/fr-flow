package frflow.decision.review

import frflow.core.name.NodeId
import frflow.decision.content.{Chain, Hash}
import frflow.decision.ledger.{Decision, Ledger}

/** Whether only words moved above a decision: its chain recomputed with the reworded nodes' meanings as they were. */
object Reworded:
  def only(all: Subjects, ledger: Ledger, s: Subject, d: Decision): Boolean =
    val was = rewordedAbove(all, ledger, s, d)
    was.nonEmpty && chainWith(all, was, s) == d.bound.chain

  /** The nodes `s` rests on whose meaning moved since `d` while their formal meaning did not: their meaning then. */
  private def rewordedAbove(all: Subjects, ledger: Ledger, s: Subject, d: Decision): Map[NodeId, Hash] =
    all.ancestry(s).flatMap(a => all.get(a).flatMap { now =>
      ledger.history(a).filter(x => x.action.binds && !x.author.at.isAfter(d.author.at)).lastOption.map(_.bound.content)
        .filter(c => Meaning.of(c) != Meaning.of(now.content) && Meaning.formal(c) == Meaning.formal(now.content))
        .map(c => a -> Meaning.of(c))
    }).toMap

  /** `s`'s chain, the reworded nodes taken as they were decided (a design keeps its own). */
  private def chainWith(all: Subjects, was: Map[NodeId, Hash], s: Subject): Chain =
    val chains = all.inOrder.foldLeft(Map.empty[NodeId, Chain])((cs, x) =>
      cs.updated(x.id, Meaning.chain(was.getOrElse(x.id, Meaning.of(x.content)), Chains.above(x, cs))))
    Chains.above(s, chains)
