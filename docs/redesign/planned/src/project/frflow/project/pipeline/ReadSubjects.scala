package frflow.project.pipeline

import frflow.core.analysis.{Fixed, Resolved}
import frflow.core.graph.{Edge, Walk}
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.Node
import frflow.decision.content.CodeNow
import frflow.decision.review.{Place, Subject, Subjects}
import frflow.project.code.{CodeFingerprints, Governance}

/** The subjects of decisions, read once off the analysis: the ledger's whole view of the knowledge base, every node
  * after all it rests on.
  */
object ReadSubjects:
  def apply(a: Analysis): Subjects =
    val r = a.decided
    val governed = Governance.of(r.theory, a.inputs.sources.keys.toList)
    val order = Walk.postorder(r.theory.refinement.nodes.map(_.id), identity)(r.restsOn)
    Subjects(order.flatMap(r.theory.node).map(n =>
      Subject(n.id, Contents.of(r, n.id), place(r, n), governed.get(n.id).map(code(a, _)), ReadProof.of(a, n))))

  private def place(r: Resolved, n: Node): Place =
    Place(r.theory.refinement.parents(n.id), r.restsOn(n.id), rivals(r, n), n.statement.kind)

  /** The nodes it replaces or that replace it, and the other definitions of a term it defines. */
  private def rivals(r: Resolved, n: Node): List[NodeId] =
    val replacing = r.theory.edges.collect {
      case Edge.Replaces(a, o) if o == n.id => a
      case Edge.Replaces(a, o) if a == n.id => o
    }
    val defining = Fixed.of(n.statement).flatMap(f =>
      r.theory.refinement.nodes.filter(m => m.id != n.id && Fixed.of(m.statement).contains(f)).map(_.id))
    (replacing ++ defining).distinct

  private def code(a: Analysis, files: List[RelPath]): CodeNow =
    CodeFingerprints.of(files.map(f => f -> a.inputs.sources.get(f)))
