package frflow
package ledger

import frflow.protocol.*

/** The snapshot with the developer's position on each node and what they read to decide it; and the
  * decided nodes that are gone from the model.
  */
object Annotate:

  def apply(v: View): Annotated =
    val nodes = v.graph.nodes.map(n => Reviewed(n, review(v, n)))
    val gone = v.ledger.decisions.keys.toList.sorted.filter(id => !v.graph.byId.contains(id) && v.ledger.binding(id).isDefined)
      .flatMap(id => v.ledger.current(id).map(Gone(id, _)))
    Annotated(v.snapshot, nodes, gone, v.graph.order)

  private def review(v: View, n: SnapNode): Review =
    val id = n.id
    val l = v.ledger
    val st = v.state(n)
    Review(
      state = st,
      causes = v.causes(n),
      version = v.version(n),
      waitsFor = v.waitsFor(n),
      moved = Downstream.moved(v, n),
      decision = l.chosen(id),
      reasonNow = l.binding(id).map(_ => Reasons.now(l, id)),
      notMechanical = v.notMechanical.getOrElse(id, v.mechanical(n)),
      resembles = resembles(l, n),
      unproven = Proofs.unproven(n),
      sameAs = sameAs(v.graph, n),
      rejectedBeside = n.parents.flatMap(l.rejectedUnder).distinctBy(_._1).filter(_._1 != id)
        .map((r, c, why) => RejectedBeside(r, c.statement, c.why, why)),
      below = if st == ReviewState.Accepted then Nil else Downstream.below(v, n),
      history = l.history(id),
      rivals = v.graph.rivals.getOrElse(id, Nil),
      alternatives = l.alternatives(id).map(Alternative(_, _)))

  /** Siblings that say formally the same: the statement may claim more than the spec. */
  private def sameAs(g: Graph, n: SnapNode): List[NodeId] =
    def sources(m: SnapNode) = m.content("sources").flatMap(_.asObject).filter(_.nonEmpty).map(o => Content.of(o).hash)
    n.parents.flatMap(g.children.getOrElse(_, Nil)).distinctBy(_.id)
      .filter(m => m.id != n.id && m.kind == n.kind && sources(m).isDefined && sources(m) == sources(n)).map(_.id)

  /** Rejected nodes a proposal says the same as (under another id, or reworded only in its `why`):
    * the developer sees why they were rejected.
    */
  private def resembles(ledger: Ledger, n: SnapNode): List[Resembling] =
    val mine = n.content
    // The same formal content (what Lean checks), however it is worded or named; or the same statement.
    def same(c: Content) = (Meaning.formula(c) == Meaning.formula(mine) && Meaning.hasFormal(c)) ||
      c.str("statement").exists(st => mine.str("statement").contains(st))
    if ledger.binding(n.id).isDefined then Nil
    else ledger.decisions.toList.sortBy(_._1).flatMap((other, ds) =>
      ds.lastOption.filter(d => other != n.id && d.action == Action.Reject && same(d.content)).map(d => Resembling(other, d.reason)))
