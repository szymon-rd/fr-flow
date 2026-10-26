package frflow.api.node

import frflow.core.analysis.{Resolve, Shown}
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}
import frflow.decision.content.FieldValue
import frflow.decision.review.{ReviewState, Standing}
import frflow.project.pipeline.Analysis
import frflow.proof.verdict.CheckStatus

/** Each group of a node's view, one function each, from the analysis. */
final class NodeViews(a: Analysis):
  private val r = a.decided

  def of(n: Node): NodeView = NodeView(n.id, says(n), placement(n.id), proof(n.id), code(n.id), review(n.id))

  def says(n: Node): Says =
    val written = a.subjects.get(n.id).flatMap(_.content.get("sources")).collect { case FieldValue.Record(fs) => fs }
    Says(n.statement.kind, n.prose.statement, n.prose.why, written.getOrElse(Nil), Resolve.mentions(r.theory, n.id))

  def placement(id: NodeId): Placement =
    val g = r.theory.refinement
    def inverse(f: NodeId => List[NodeId]) = g.nodes.map(_.id).filter(f(_).contains(id))
    val related = List(
      Relation.Parent -> g.parents(id), Relation.Part -> g.parts(id),
      Relation.Design -> g.children(id).filter(c => g.node(c).exists(_.statement.kind == NodeKind.Design)),
      Relation.Uses -> r.usesOf(id), Relation.UsedBy -> inverse(r.usesOf),
      Relation.Calls -> r.callsOf(id), Relation.CalledBy -> inverse(r.callsOf),
      Relation.Keeps -> r.theory.edges.collect { case Edge.Keeps(`id`, i, _) => i },
      Relation.KeptBy -> r.theory.edges.collect { case Edge.Keeps(c, `id`, _) => c },
      Relation.Rival -> a.subjects.get(id).toList.flatMap(_.place.rivals))
    Placement(g.roots.exists(_.id == id), related.flatMap((rel, ns) => ns.map(rel -> _)))

  def proof(id: NodeId): ProofView =
    val check = a.inputs.recorded.checks.get(id)
    ProofView(check.fold(CheckStatus.Unchecked)(_.status), check.toList.flatMap(_.results),
      check.toList.flatMap(_.findings), a.computed.examples.getOrElse(id, Nil), a.inputs.proofs.contains(id))

  def code(id: NodeId): Option[CodeView] =
    Option.when(r.theory.code.attached.contains(id) || r.theory.code.realized.contains(id))(CodeView(
      Shown.of(r.theory, id), r.theory.code.attached.get(id).flatMap(_.runCheck),
      a.inputs.recorded.tests.get(id).map(_._2)))

  def review(id: NodeId): ReviewView =
    val subject = a.subjects.get(id)
    ReviewView(a.standings.getOrElse(id, Standing(ReviewState.Proposed, Nil)), a.inputs.ledger.binding(id),
      subject.flatMap(a.reading.waitsFor), a.reading.notMechanical.get(id).flatten)
