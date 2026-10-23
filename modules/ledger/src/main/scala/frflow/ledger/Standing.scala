package frflow
package ledger

import frflow.protocol.*
import ReviewState.{Accepted, Proposed, Rejected}

/** Where the developer stands on a node (its state) and what moved under its decision (its causes).
  *
  * The rule: a decision binds a person's reason to the hash of what they saw. Whatever moves under it
  * puts the node back up for review: `self` (what the node itself says), `above` (the meaning of what it
  * rests on, however far up; or a parent rejected), `parts` (a part added or removed), `code` (the code
  * it governs), `revisit` (the developer asked), `merged` (two branches decided it and a merge kept both).
  */
final case class Standing(state: ReviewState, causes: List[Cause])

object Standing:

  /** Every node's standing, in one pass over the nodes, each after all it rests on. */
  def all(g: Graph, ledger: Ledger): Map[NodeId, Standing] =
    g.order.flatMap(g.byId.get).foldLeft(Map.empty[NodeId, Standing])((done, n) => done.updated(n.id, of(g, ledger, done, n)))

  /** A node's standing, given the standings of what it rests on. */
  def of(g: Graph, ledger: Ledger, done: Map[NodeId, Standing], n: SnapNode): Standing =
    // A node whose parent was rejected is reviewed as if its parent's meaning moved: what it rests on is
    // no longer chosen.
    val parentRejected = n.parents.exists(p => done.get(p).exists(_.state == Rejected))
    val causes = ledger.binding(n.id).fold(Nil)(d => movedUnder(g, ledger, n, d, parentRejected))
    Standing(state(ledger, n, causes), causes)

  private def state(ledger: Ledger, n: SnapNode, causes: List[Cause]): ReviewState =
    ledger.current(n.id) match
      case Some(d) if d.action == Action.Reject => if d.hash == n.hash then Rejected else Proposed
      case Some(d) if d.action.binds || d.action == Action.Revisit => if causes.nonEmpty then ReviewState.Review else Accepted
      case _ => Proposed

  private def movedUnder(g: Graph, ledger: Ledger, n: SnapNode, d: Decision, parentRejected: Boolean): List[Cause] =
    val moved = d.hash != n.hash
    List(
      Cause.Self -> (moved && Meaning.selfChanged(d.content, n.content)),
      Cause.Above -> ((d.chain != g.parentChain(n) && !reworded(g, ledger, n, d)) || parentRejected),
      Cause.Parts -> (moved && Meaning.partsChanged(d.content, n.content)),
      Cause.Code -> (d.code != n.code.map(_.fingerprint)),
      Cause.Revisit -> ledger.current(n.id).exists(_.action == Action.Revisit),
      Cause.Merged -> ledger.forked(n.id)
    ).collect { case (c, true) => c }

  /** Whether what `n` rests on moved only in its words: with each formal node above it whose Lean did
    * not change (its statement reworded) taken as it was decided when `d` was, the chain is `d`'s again.
    * Rewording a formal node reviews that node only; the decisions below it are listed under it (`below`),
    * not sent to review.
    */
  private def reworded(g: Graph, ledger: Ledger, n: SnapNode, d: Decision): Boolean =
    val rests = g.ancestry(n).toSet
    val was: Map[NodeId, Hash] = rests.toList.flatMap(a => g.byId.get(a).toList.flatMap { now =>
      ledger.history(a).filter(x => x.action.binds && !x.at.isAfter(d.at)).lastOption.map(_.content)
        .filter(c => Meaning.hasFormal(now.content) && Meaning.of(c) != Meaning.of(now.content) &&
          Meaning.formal(c) == Meaning.formal(now.content))
        .map(c => a -> Meaning.of(c))
    }).toMap
    def touched(x: SnapNode, touchedAbove: Set[NodeId]) = g.restsOn(x).exists(a => was.contains(a) || touchedAbove(a))
    // As `Graph.parentChain`, with the reworded nodes as decided; a design node keeps its own.
    def restOf(x: SnapNode, isTouched: Boolean, chains: Map[NodeId, Chain]) =
      if !isTouched || x.kind == NodeKind.Design then g.parentChain(x)
      else Meaning.above(Chain.empty, g.restsOn(x).map(chains.getOrElse(_, Chain.empty)))
    was.nonEmpty && {
      val (touchedAbove, chains) = g.order.filter(rests).flatMap(g.byId.get)
        .foldLeft((Set.empty[NodeId], Map.empty[NodeId, Chain])) { case ((t, cs), x) =>
          val isTouched = touched(x, t)
          (if isTouched then t + x.id else t,
            cs.updated(x.id, Meaning.chainOf(was.getOrElse(x.id, Meaning.of(x.content)), restOf(x, isTouched, cs))))
        }
      restOf(n, touched(n, touchedAbove), chains) == d.chain
    }
