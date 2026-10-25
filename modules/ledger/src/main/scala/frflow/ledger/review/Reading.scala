package frflow
package ledger
package review

import frflow.protocol.*
import ReviewState.{Accepted, Proposed, Rejected}

/** A snapshot read with a ledger: each node's standing, wait and mechanical answer computed once, parents first. */
final class Reading(val graph: Graph, val ledger: Ledger):
  def snapshot: Snapshot = graph.snapshot
  lazy val standings: Map[NodeId, Standing] = Standing.all(graph, ledger)
  def standing(n: SnapNode): Standing = standings.getOrElse(n.id, Standing.of(graph, ledger, standings, n))
  def state(n: SnapNode): ReviewState = standing(n).state
  def causes(n: SnapNode): List[Cause] = standing(n).causes
  /** A node not in the model is not decided. */
  def stateOf(id: NodeId): ReviewState = graph.byId.get(id).fold(Proposed)(state)
  def holds(id: NodeId): Boolean = stateOf(id) == Accepted
  /** Where the developer stands on IDEA.md; the root is decided after it. */
  lazy val idea: Option[IdeaReview] = IdeaDecision.review(snapshot, ledger)

  /** What the developer saw of a node: a decision sent with it is refused if the node moved since. */
  def version(n: SnapNode): Version =
    Version(Sha.parts(n.hash.value, graph.parentChain(n).value, n.code.fold("")(_.fingerprint.value)).take(16))

  /** A parent not chosen; or, when `n` rests on its parents (proposed, or they moved), what it rests on not accepted. */
  def waitsFor(n: SnapNode): Option[NodeId] =
    val restsOnParent = state(n) == Proposed || causes(n).contains(Cause.Above)
    n.parents.find(p => graph.byId.get(p).map(state).exists(s => s == Proposed || s == Rejected || (restsOnParent && s != Accepted)))
      .orElse(Option.when(restsOnParent)((n.uses ++ n.relies).find(i => graph.byId.get(i).exists(x => state(x) != Accepted))).flatten)
      .orElse(Option.when(snapshot.root.contains(n.id) && idea.exists(_.state != Accepted))(IdeaDecision.Id))

  /** Why each node is not mechanical, or None if it is, parents first. */
  lazy val notMechanical: Map[NodeId, Option[String]] =
    graph.order.flatMap(graph.byId.get).foldLeft(Map.empty[NodeId, Option[String]])((done, n) =>
      done.updated(n.id, Mechanical.why(this, n, done)))
  def mechanical(n: SnapNode): Option[String] = Mechanical.why(this, n, notMechanical)
  /** The mechanical decisions, in the order they are taken: the batch `confirm` accepts. */
  def mechanicalBatch: List[NodeId] = graph.order.filter(id => notMechanical.get(id).exists(_.isEmpty))

object Reading:
  def apply(snapshot: Snapshot, ledger: Ledger): Reading = new Reading(Graph(snapshot), ledger)
  def apply(graph: Graph, ledger: Ledger): Reading = new Reading(graph, ledger)
