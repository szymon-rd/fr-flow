package frflow
package ledger

import frflow.protocol.*
import ReviewState.{Accepted, Proposed, Rejected}

/** A snapshot read with a ledger: each node's standing, what it waits for and whether it is
  * mechanical, each computed once, in one pass parents first. Made for each reading; nothing is kept
  * between readings.
  */
final class View(val graph: Graph, val ledger: Ledger):
  def snapshot: Snapshot = graph.snapshot

  lazy val standings: Map[NodeId, Standing] = Standing.all(graph, ledger)
  def standing(n: SnapNode): Standing = standings.getOrElse(n.id, Standing.of(graph, ledger, standings, n))
  def state(n: SnapNode): ReviewState = standing(n).state
  def causes(n: SnapNode): List[Cause] = standing(n).causes
  /** The state of a node by its id; a node not in the model is not decided. */
  def stateOf(id: NodeId): ReviewState = graph.byId.get(id).fold(Proposed)(state)
  /** The node holds as decided. */
  def holds(id: NodeId): Boolean = stateOf(id) == Accepted

  /** What the developer saw of a node: a decision sent with it is refused if the node moved since. */
  def version(n: SnapNode): String =
    Sha.parts(n.hash.value, graph.parentChain(n).value, n.code.fold("")(_.fingerprint.value)).take(16)

  /** The node a decision on `n` waits for: the first of its parents, when `n` rests on them (a proposal,
    * or a node whose parents moved) and it is not accepted.
    */
  def waitsFor(n: SnapNode): Option[NodeId] =
    val restsOnParent = state(n) == Proposed || causes(n).contains(Cause.Above)
    // Nothing is decided under a parent that is not chosen; what rests on a moved parent waits for it.
    n.parents.find { p =>
      graph.byId.get(p).map(state).exists(s => s == Proposed || s == Rejected || (restsOnParent && s != Accepted))
    }.orElse(
      // A node rests on the definitions it uses and the contracts its code calls, as on its parents.
      Option.when(restsOnParent)((n.uses ++ n.relies).find(i => graph.byId.get(i).exists(x => state(x) != Accepted))).flatten)

  /** Why each node is not mechanical, or None if it is (see `Mechanical`), parents first. */
  lazy val notMechanical: Map[NodeId, Option[String]] =
    graph.order.flatMap(graph.byId.get).foldLeft(Map.empty[NodeId, Option[String]])((done, n) =>
      done.updated(n.id, Mechanical.why(this, n, done)))

  def mechanical(n: SnapNode): Option[String] = Mechanical.why(this, n, notMechanical)

object View:
  def apply(snapshot: Snapshot, ledger: Ledger): View = new View(Graph(snapshot), ledger)
  /** The same structure, read with another ledger. */
  def apply(graph: Graph, ledger: Ledger): View = new View(graph, ledger)
