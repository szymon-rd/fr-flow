package frflow.api.view

import cats.syntax.all.*
import frflow.api.node.{CodeView, NodeView, NodeViews, Relation}
import frflow.core.checking.Checking
import frflow.core.name.NodeId
import frflow.eval.run.OnCode
import frflow.project.pipeline.Analysis
import frflow.proof.verdict.{CheckStatus, ObligationStatus}

/** The read side: the view derived from the analysis, and what front ends print of it (`tree`, `inbox`, `beside`,
  * `above`, the overview) as functions of the view.
  */
object Views:
  def of(a: Analysis, warnings: List[Warning]): View =
    val views = NodeViews(a)
    val nodes = a.subjects.inOrder.flatMap(s => a.decided.theory.node(s.id)).map(views.of)
    val whole = Wholes.of(a)
    View(nodes, a.decided.theory.refinement.roots.map(_.id), whole, overview(nodes, whole),
      warnings ++ Wholes.warnings(whole) ++ unchecked(a))

  /** `status` says it of each claim nothing checks (`Checking.unchecked`): its parts do not prove it, and the plain
    * Scala it is about cannot be tested against it.
    */
  def unchecked(a: Analysis): List[Warning] =
    a.decided.theory.nodes.map(_.node.id).filter(Checking.unchecked(a.decided.theory, _)).map(Warning.NotChecked(_))

  def overview(nodes: List[NodeView], whole: WholeView): Overview = Overview(
    nodes.foldMap(n => Tally.one(n.review.standing.state)), nodes.foldMap(n => Tally.one(n.proof.status)),
    nodes.foldMap(_.code.foldMap(pieces)), whole.groups.foldMap(g => Tally.one(g.status)),
    whole.examples.foldMap(e =>
      Tally.one(e.onClaims == OnClaims.Lean(ObligationStatus.Proven) && e.onCode == OnCode.Holds)),
    nodes.forall(_.proof.status == CheckStatus.Proven) && whole.groups.forall(_.status == GroupStatus.Proven))

  private def pieces(c: CodeView): Tally[Piece] =
    c.shown.proven.foldMap(_ => Tally.one(Piece.Proven)) |+| c.shown.tested.foldMap(_ => Tally.one(Piece.Tested)) |+|
      c.shown.assumed.foldMap(_ => Tally.one(Piece.Assumed))

  /** Under each parent of `id`, the other parts that with it make the parent. */
  def beside(v: View, id: NodeId): List[(NodeId, List[NodeId])] =
    v.node(id).toList.flatMap(_.place(Relation.Parent)).map(p =>
      p -> v.node(p).toList.flatMap(_.place(Relation.Part)).filterNot(_ == id))

  def tree(v: View, from: Option[NodeId]): List[(Int, NodeId)] = ???
  def inbox(v: View, aside: Set[NodeId]): List[NodeId] = ???
