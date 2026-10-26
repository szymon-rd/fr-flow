package frflow.api.node

import frflow.core.analysis.{Constrained, Resolve}
import frflow.core.checking.Shown
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}
import frflow.decision.content.FieldValue
import frflow.decision.review.{ReviewState, Standing}
import frflow.project.pipeline.{Analysis, Texts}
import frflow.proof.verdict.CheckStatus

/** Each group of a node's view, one function each, from the analysis. */
final class NodeViews(a: Analysis):
  private val r = a.decided

  def of(n: Node): NodeView = NodeView(n.id, says(n), placement(n.id), proof(n.id), code(n.id), review(n.id))

  def says(n: Node): Says =
    val written = a.subjects.get(n.id).flatMap(_.content.get("formula")).collect { case FieldValue.Text(f) => f }
    Says(n.statement.kind, n.says, written, Texts.checking(r.theory, n.id), Resolve.mentions(r.theory, n.id),
      a.inputs.ledger.binding(n.id).map(_.reason.text))

  def placement(id: NodeId): Placement =
    val g = r.theory.refinement
    def inverse(f: NodeId => List[NodeId]) = g.nodes.map(_.id).filter(f(_).contains(id))
    val related = List(
      Relation.Parent -> g.parents(id), Relation.Part -> g.parts(id),
      Relation.Design -> g.children(id).filter(c => g.node(c).exists(_.statement.kind == NodeKind.Design)),
      Relation.Calls -> r.callsOf(id), Relation.CalledBy -> inverse(r.callsOf),
      Relation.Assumes -> g.assumed(id), Relation.AssumedBy -> inverse(g.assumed),
      Relation.Rival -> a.subjects.get(id).toList.flatMap(_.place.rivals))
    Placement(g.roots.exists(_.id == id), related.flatMap((rel, ns) => ns.map(rel -> _)))

  def proof(id: NodeId): ProofView =
    val check = a.inputs.recorded.checks.get(id)
    ProofView(check.fold(CheckStatus.Unchecked)(_.status), check.toList.flatMap(_.results),
      check.toList.flatMap(_.findings), a.inputs.proofs.contains(id))

  def code(id: NodeId): Option[CodeView] =
    val coded = Constrained.of(r.theory, id).exists(r.theory.code.attached.contains)
    val modelled = r.theory.node(id).flatMap(_.statement.outside).exists {
      case OutsideFact.BehavesAs(b, _) => r.theory.code.realized.contains(b)
      case _                           => false
    }
    Option.when(coded || modelled)(
      CodeView(Shown.of(r.theory, id), a.inputs.recorded.tests.get(id).map(_._2)))

  def review(id: NodeId): ReviewView =
    val subject = a.subjects.get(id)
    ReviewView(a.standings.getOrElse(id, Standing(ReviewState.Proposed, Nil)), a.inputs.ledger.binding(id),
      subject.flatMap(a.reading.waitsFor), a.reading.notMechanical.get(id).flatten)
