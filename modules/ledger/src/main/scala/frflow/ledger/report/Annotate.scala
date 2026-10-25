package frflow
package ledger
package report

import frflow.protocol.*

/** The snapshot with the developer's position on each node and what they read to decide it, and the decided nodes gone. */
object Annotate:
  def apply(snapshot: Snapshot, ledger: Ledger): Annotated = apply(Reading(snapshot, ledger))

  def apply(v: Reading): Annotated =
    val l = v.ledger
    val nodes = v.graph.nodes.map { n =>
      val id = n.id
      val st = v.state(n)
      Reviewed(n, Review(state = st, causes = v.causes(n), version = v.version(n), waitsFor = v.waitsFor(n),
        moved = Downstream.moved(v, n), decision = l.chosen(id), binding = l.binding(id),
        reasonNow = l.binding(id).map(_ => Reasons.now(l, id)), notMechanical = v.notMechanical.getOrElse(id, v.mechanical(n)),
        unproven = Proofs.unproven(n),
        rejectedBeside = n.parents.flatMap(l.rejectedUnder).distinctBy(_._1).filter(_._1 != id)
          .map((r, c, why) => RejectedBeside(r, c.statement, c.why, why)),
        below = if st == ReviewState.Accepted then Nil else Downstream.below(v, n),
        history = l.history(id), rivals = v.graph.rivals.getOrElse(id, Nil), alternatives = l.alternatives(id).map(Alternative(_, _))))
    }
    val gone = l.decisions.keys.toList.sorted.filter(id => id != IdeaDecision.Id && !v.graph.byId.contains(id) && l.binding(id).isDefined)
      .flatMap(id => l.current(id).map(Gone(id, _)))
    Annotated(v.snapshot, nodes, gone, v.graph.order, v.idea)
