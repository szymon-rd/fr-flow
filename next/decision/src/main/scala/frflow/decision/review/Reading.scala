package frflow.decision.review

import frflow.core.name.NodeId
import frflow.decision.content.Sha
import frflow.decision.ledger.{Bound, Ledger}

/** The subjects read with a ledger: each node's standing, what it waits for and whether it is mechanical, computed
  * once, parents first.
  */
final class Reading(val subjects: Subjects, val ledger: Ledger):
  lazy val standings: Map[NodeId, Standing] = Standings(subjects, ledger).all
  lazy val chains: Map[NodeId, frflow.decision.content.Chain] = Chains.of(subjects)
  def state(id: NodeId): ReviewState = standings.get(id).fold(ReviewState.Proposed)(_.state)
  def causes(id: NodeId): List[Cause] = standings.get(id).fold(Nil)(_.causes)
  /** What the developer saw of a node: a decision sent with it is refused if it moved since. */
  def version(s: Subject): String =
    Sha.parts(s.content.hash.value, Chains.above(s, chains).value, s.code.fold("")(_.fingerprint.sha)).take(16)
  /** The decided nodes no longer in the model, for `gone`. */
  def gone: List[NodeId] =
    ledger.decisions.keys.toList.sortBy(_.value)
      .filter(id => subjects.get(id).isEmpty && ledger.binding(id).isDefined)
  /** What a decision about `s` taken now is bound to: its content, its chain, its code's fingerprint. */
  def bound(s: Subject): Bound = Bound(s.content, Chains.above(s, chains), s.code.map(_.fingerprint))

  def children(id: NodeId): List[Subject] = subjects.childrenOf(id)
  /** The first node `s` rests on that is not accepted, when it waits for one (docs/DAG.md §5, Order): a parent not
    * chosen; or, for a proposal or a node whose `above` moved, its first parent, then premise or callee, not accepted.
    */
  def waitsFor(s: Subject): Option[NodeId] =
    val resting = state(s.id) == ReviewState.Proposed || causes(s.id).contains(Cause.Above)
    def notAccepted(id: NodeId) = subjects.get(id).isDefined && state(id) != ReviewState.Accepted
    def notChosen(id: NodeId) = subjects.get(id).isDefined &&
      (state(id) == ReviewState.Proposed || state(id) == ReviewState.Rejected)
    s.place.parents.find(p => notChosen(p) || (resting && notAccepted(p)))
      .orElse(s.place.restsOn.filterNot(s.place.parents.contains).find(notAccepted).filter(_ => resting))
  /** Why a node is not mechanical, or none: the batch `confirm` accepts, parents first. */
  lazy val notMechanical: Map[NodeId, Option[Mechanical.Not]] =
    subjects.inOrder.foldLeft(Map.empty[NodeId, Option[Mechanical.Not]])((done, s) =>
      done.updated(s.id, Mechanical.why(this, s, done)))
