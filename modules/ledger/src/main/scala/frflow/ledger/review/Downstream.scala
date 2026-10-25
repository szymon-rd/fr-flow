package frflow
package ledger
package review

import frflow.protocol.*
import scala.annotation.tailrec
import ReviewState.Accepted

/** How a change travels: the ancestors whose meaning moved under a node, and the decisions below a changed node. */
object Downstream:
  /** The ancestors whose meaning changed since the node was decided, nearest first, each with its content then. */
  def moved(v: Reading, n: SnapNode): List[Moved] =
    v.ledger.binding(n.id).filter(d => d.chain != v.graph.parentChain(n) && v.causes(n).contains(Cause.Above)).fold(Nil) { d =>
      // What it rests on: its ancestors, the definitions they use, and the contracts their code calls.
      val above = v.graph.ancestors(n)
      (above ++ (n :: above).flatMap(x => x.uses ++ x.relies).distinct.flatMap(v.graph.byId.get)).distinctBy(_.id).flatMap { a =>
        v.ledger.history(a.id).filter(x => x.action.binds && !x.at.isAfter(d.at)).lastOption
          .filter(t => Meaning.of(t.content) != Meaning.of(a.content)).map(t => Moved(a.id, t.content))
      }
    }

  /** The decisions below `n` that accepting it can act on, parents first, each once: those accepted, and those under
    * review only because `n`'s meaning moved. Below a node under review for anything else, nothing: it is decided first.
    */
  def below(v: Reading, n: SnapNode): List[Below] =
    val g = v.graph
    def row(c: SnapNode, kind: BelowKind) =
      Below(c.id, kind, c.content.statement, Reasons.now(v.ledger, c.id), v.ledger.chosen(c.id).fold("")(_.reason), c.content.why)
    // Moved only by this node, or by nodes above it already accepted again.
    def movedOnlyBy(c: SnapNode) = v.causes(c) == List(Cause.Above) && moved(v, c).map(_.id).forall(m => m == n.id || v.holds(m))
    def listed(c: SnapNode): Option[Below] =
      if v.state(c) == Accepted && v.ledger.binding(c.id).isDefined then Some(row(c, BelowKind.Accepted))
      else Option.when(v.state(c) == ReviewState.Review && movedOnlyBy(c))(row(c, BelowKind.Moved))
    @tailrec def walk(frontier: List[SnapNode], seen: Set[NodeId], found: Vector[Below]): Vector[Below] =
      if frontier.isEmpty then found
      else
        val fresh = frontier.distinctBy(_.id).filterNot(c => seen(c.id))
        val rows = fresh.flatMap(c => listed(c).map(c -> _))
        walk(rows.flatMap((c, _) => g.dependentsOf(c.id)), seen ++ fresh.map(_.id), found ++ rows.map(_._2))
    walk(g.dependentsOf(n.id), Set(n.id), Vector.empty).toList.sortBy(b => g.rank.getOrElse(b.id, Int.MaxValue))
