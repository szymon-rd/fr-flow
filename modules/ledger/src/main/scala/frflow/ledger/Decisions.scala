package frflow
package ledger

import frflow.protocol.*

/** The developer's position on each node, computed from the snapshot and the ledger, and the one way to
  * record a decision: the entry points other modules call. Each reads the snapshot and ledger afresh
  * (a `View`); see `Standing` for the states and causes, `Decide` for the rules of a decision.
  */
object Decisions:

  /** The snapshot with each node's state, what moved, its decision, history and alternatives; and the
    * decided nodes that are gone from the model.
    */
  def annotate(snapshot: Snapshot, ledger: Ledger): Annotated = Annotate(View(snapshot, ledger))

  /** Applies a decision: the new ledger, or why it is refused (see `Decide`). */
  def decide(snapshot: Snapshot, ledger: Ledger, r: DecisionRequest, at: String, commit: Option[String] = None,
      tree: Option[String] = None): Either[Refusal, Ledger] =
    Decide(snapshot, ledger, r, Stamp(at, commit, tree))

  def state(snapshot: Snapshot, ledger: Ledger, n: SnapNode): ReviewState = View(snapshot, ledger).state(n)

  /** What moved under a node's decision. */
  def causes(snapshot: Snapshot, ledger: Ledger, n: SnapNode): List[Cause] = View(snapshot, ledger).causes(n)

  /** Why `n` is not mechanical, or None if it is (see `Mechanical`). */
  def mechanical(snapshot: Snapshot, ledger: Ledger, n: SnapNode): Option[String] = View(snapshot, ledger).mechanical(n)

  /** What a node rests on, as decided (see `Graph.parentChain`). */
  def parentChain(snapshot: Snapshot, n: SnapNode): Chain = Graph(snapshot).parentChainAlone(n)

  /** Every node after all it rests on: the order decisions are taken in, a batch's too. */
  def order(snapshot: Snapshot): List[NodeId] = Graph(snapshot).order

  def alternatives(a: SnapNode, b: SnapNode): Boolean = Graph.alternatives(a, b)
  def ideaSections(decided: String): (String, List[(String, String)]) = Idea.sections(decided)
  def splitIdea(idea: String): (String, String) = Idea.split(idea)
