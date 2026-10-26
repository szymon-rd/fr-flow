package frflow.api.view

import cats.syntax.all.*
import frflow.api.node.{CodeView, NodeView, NodeViews, Relation}
import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis

/** The read side: the view derived from the analysis, and what front ends print of it (`tree`, `inbox`, `beside`,
  * `above`, the overview) as functions of the view.
  */
object Views:
  def of(a: Analysis, warnings: List[Warning]): View =
    val views = NodeViews(a)
    val nodes = a.subjects.inOrder.flatMap(s => a.decided.theory.node(s.id)).map(views.of)
    View(nodes, a.decided.theory.refinement.roots.headOption.map(_.id), overview(nodes), warnings)

  def overview(nodes: List[NodeView]): Overview = Overview(
    nodes.foldMap(n => Tally.one(n.review.standing.state)), nodes.foldMap(n => Tally.one(n.proof.status)),
    nodes.foldMap(_.code.foldMap(pieces)), nodes.foldMap(_.code.flatMap(_.runCheck).foldMap(Tally.one)),
    nodes.foldMap(_.proof.examples.foldMap(e => Tally.one(e.onPromise == frflow.eval.run.Agreement.Agrees))),
    nodes.forall(_.proof.status == frflow.proof.verdict.CheckStatus.Proven))

  private def pieces(c: CodeView): Tally[Piece] =
    c.shown.proven.foldMap(_ => Tally.one(Piece.Proven)) |+| c.shown.tested.foldMap(_ => Tally.one(Piece.Tested)) |+|
      c.shown.assumed.foldMap(_ => Tally.one(Piece.Assumed))

  /** Under each parent of `id`, the other parts that with it make the parent. */
  def beside(v: View, id: NodeId): List[(NodeId, List[NodeId])] =
    v.node(id).toList.flatMap(_.place(Relation.Parent)).map(p =>
      p -> v.node(p).toList.flatMap(_.place(Relation.Part)).filterNot(_ == id))

  def tree(v: View, from: Option[NodeId]): List[(Int, NodeId)] = ???
  def inbox(v: View, aside: Set[NodeId]): List[NodeId] = ???
