package frflow
package ledger

import frflow.protocol.*
import scala.annotation.tailrec

/** How a change travels: the ancestors whose meaning moved under a node, and the decisions below a
  * changed node that accepting it can act on.
  */
object Downstream:

  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its
    * content as it was then: what is shown for the cause `above`.
    */
  def moved(v: View, n: SnapNode): List[Moved] =
    v.ledger.binding(n.id).filter(d => d.chain != v.graph.parentChain(n) && v.causes(n).contains(Cause.Above)).fold(Nil) { d =>
      // What it rests on: its ancestors, the definitions they use, and the contracts their code calls.
      val above = v.graph.ancestors(n)
      (above ++ (n :: above).flatMap(x => x.uses ++ x.relies).distinct.flatMap(v.graph.byId.get)).distinctBy(_.id).flatMap { a =>
        v.ledger.history(a.id).filter(x => x.action.binds && x.at <= d.at).lastOption
          .filter(t => Meaning.of(t.content) != Meaning.of(a.content)).map(t => Moved(a.id, t.content))
      }
    }

  /** The decisions below `n` that accepting it can act on, with their reasons, parents first: those
    * accepted (each may be revisited), and those under review only because `n`'s meaning moved
    * (each still holds, or is revisited). Below a node that is under review for anything else,
    * nothing is listed: that node is decided on its own first.
    */
  def below(v: View, n: SnapNode): List[Below] =
    val g = v.graph
    def accepted(c: SnapNode) = v.state(c) == ReviewState.Accepted && v.ledger.binding(c.id).isDefined
    def row(c: SnapNode, kind: BelowKind) =
      Below(c.id, kind, c.content.statement, Reasons.now(v.ledger, c.id), v.ledger.chosen(c.id).fold("")(_.reason), c.content.why)
    // Moved only by this node, or by nodes above it already accepted again.
    def movedOnlyBy(c: SnapNode) = v.causes(c) == List(Cause.Above) &&
      moved(v, c).map(_.id).forall(m => m == n.id || v.holds(m))
    def listed(c: SnapNode): Option[Below] =
      if accepted(c) then Some(row(c, BelowKind.Accepted))
      else Option.when(v.state(c) == ReviewState.Review && movedOnlyBy(c))(row(c, BelowKind.Moved))
    // What rests on it, however far down (its parts and theirs; the users of a definition, the callers
    // of a contract, the keepers of an invariant, and what rests on them), through the decisions listed;
    // each once, however many paths lead to it.
    @tailrec def walk(frontier: List[SnapNode], seen: Set[NodeId], found: Vector[Below]): Vector[Below] =
      if frontier.isEmpty then found
      else
        val fresh = frontier.distinctBy(_.id).filterNot(c => seen(c.id))
        val rows = fresh.flatMap(c => listed(c).map(c -> _))
        walk(rows.flatMap((c, _) => g.dependentsOf(c.id)), seen ++ fresh.map(_.id), found ++ rows.map(_._2))
    val own = walk(g.dependentsOf(n.id), Set(n.id), Vector.empty).toList.sortBy(b => g.rank.getOrElse(b.id, Int.MaxValue))
    // The idea is what every decision rests on: a root's change lists the decisions outside its tree too.
    val elsewhere =
      if !n.isRoot || n.content("ideaSection").isDefined then Nil
      else g.nodes.filter(c => c.id != n.id && !own.exists(_.id == c.id) && !g.ancestors(c).exists(_.id == n.id) && accepted(c))
        .map(row(_, BelowKind.Accepted))
    // The invariants cut across every concern: a change to a root's idea lists them too.
    val across =
      if !n.isRoot then Nil
      else g.nodes.filter(c => c.rule && !(own ++ elsewhere).exists(_.id == c.id) && accepted(c)).map(row(_, BelowKind.Accepted))
    own ++ elsewhere ++ across
