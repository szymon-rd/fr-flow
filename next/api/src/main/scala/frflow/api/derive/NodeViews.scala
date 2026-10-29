package frflow.api.derive

import frflow.api.node.*
import frflow.core.analysis.{Constrained, Resolve}
import frflow.core.checking.Shown
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{Node, NodeKind}
import frflow.decision.content.FieldValue
import frflow.decision.review.{Moves, ReviewState, Standing}
import frflow.project.pipeline.{Analysis, Texts}
import frflow.core.analysis.outside.{Outsides, Reads}

/** Each group of a node's view, one function each, from the analysis. */
private[api] final class NodeViews(a: Analysis):
  private val r = a.decided
  private val counting = a.inputs.ledger.counting

  def of(n: Node): NodeView = NodeView(n.id, says(n), placement(n.id), proof(n.id), code(n.id), review(n.id))

  def says(n: Node): Says =
    val written = a.subjects.get(n.id).flatMap(_.content.get("written")).collect { case FieldValue.Text(f) => f }
    Says(n.statement.kind, n.says, written, Texts.checking(r.theory, n.id), Resolve.mentions(r.theory, n.id),
      counting.binding(n.id).map(_.reason.text))

  def placement(id: NodeId): Placement =
    val g = r.theory.refinement
    def inverse(f: NodeId => List[NodeId]) = g.nodes.map(_.id).filter(f(_).contains(id))
    val rules = (g.rules(id) ++ g.assumed(id).filter(p => g.node(p).exists(_.statement.rule))).distinct
    val (taken, unused) = rules.partition(Reads.takes(r.theory, id, _))
    val related = List(
      Relation.Parent -> g.parents(id), Relation.Part -> g.parts(id), Relation.Rule -> taken,
      Relation.UnusedRule -> unused,
      Relation.Design -> g.children(id).filter(c => g.node(c).exists(_.statement.kind == NodeKind.Design)),
      Relation.Calls -> r.callsOf(id), Relation.CalledBy -> inverse(r.callsOf),
      Relation.Assumes -> g.assumed(id), Relation.AssumedBy -> inverse(g.assumed),
      Relation.Rival -> a.subjects.get(id).toList.flatMap(_.place.rivals))
    Placement(g.roots.exists(_.id == id), related.flatMap((rel, ns) => ns.map(rel -> _)))

  def proof(id: NodeId): ProofView =
    val check = a.current(id)
    ProofView(check.fold(Leans.Unchecked)(c => Leans.state(c.status)), check.toList.flatMap(_.results).map(Leans.of),
      check.toList.flatMap(_.findings).map(Leans.finding), a.inputs.lean.proofs.contains(id),
      a.subjects.get(id).toList.flatMap(_.proof.unproven))

  def code(id: NodeId): Option[CodeView] =
    val coded = Constrained.of(r.theory, id).exists(r.theory.code.attached.contains)
    val models = a.models(id)
    // A model's runs are shown beside the assumption that only the code changes its state, or, with none, beside
    // each node resting on its Scala; every node resting on them is gated by them all the same (`ReadProof`).
    val shown = models.find(m => Outsides.onlyCodeChanges(r.theory, m).forall(_ == id))
    val tests = a.tested(id).orElse(shown.flatMap(a.testedModel))
    Option.when(coded || models.nonEmpty)(CodeView(Shown.of(r.theory, id), tests.map(Tests.of(_, operations))))

  /** A model's operations, in the order its meanings are given. */
  private def operations(m: ModelName): List[SymbolName] = r.theory.vocabulary.model(m).toList.flatMap(_.ops.map(_.op))

  def review(id: NodeId): ReviewView =
    val subject = a.subjects.get(id)
    ReviewView(subject.fold("")(a.reading.version), a.standings.getOrElse(id, Standing(ReviewState.Proposed, Nil)),
      Decisions(counting.binding(id), counting.current(id)), subject.flatMap(a.reading.waitsFor),
      a.reading.notMechanical.get(id).flatten, Movement(subject.toList.flatMap(Moves.movedAbove(a.reading, _))
        .map(_._1), subject.toList.flatMap(Moves.actsOn(a.reading, _)).map(_.id)))
