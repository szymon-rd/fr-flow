package frflow.project.pipeline

import frflow.core.analysis.Resolved
import frflow.core.graph.{Edge, Walk}
import frflow.core.name.NodeId
import frflow.core.spec.Node
import frflow.decision.review.{Place, Subject, Subjects}

/** The subjects of decisions, read once off the analysis: the ledger's whole view of the knowledge base, every node
  * after all it rests on (its parents, the premises it assumes, the callees it relies on), in the model's order
  * otherwise.
  */
object ReadSubjects:
  def apply(a: Analysis): Subjects =
    val r = a.decided
    val places = r.theory.refinement.nodes.map(n => n.id -> place(r, n)).toMap
    val order = Walk.postorder(r.theory.refinement.nodes.map(_.id), identity)(places.get(_).fold(Nil)(_.restsOn))
    Subjects(order.flatMap(r.theory.node).map(n =>
      Subject(n.id, Contents.of(r, n.id), places(n.id), a.governed.get(n.id), ReadProof.of(a, n))))

  /** Its parents are the wholes it is a part of only: a premise rests on nothing that assumes it, so the nodes
    * assuming it are below it in no order; what it assumes is among what it rests on. Nothing below it is: a node
    * proven of code relies on the statements about what its code calls, and those its own parts state are decided
    * after it, as parts are.
    */
  def place(r: Resolved, n: Node): Place =
    val below = r.theory.refinement.nodes.map(_.id).filter(r.theory.refinement.ancestors(_).contains(n.id)).toSet
    Place(r.theory.refinement.parents(n.id), r.restsOn(n.id).filterNot(below), rivals(r, n), n.statement.kind)

  /** The nodes it replaces or that replace it. */
  private def rivals(r: Resolved, n: Node): List[NodeId] =
    r.theory.edges.collect {
      case Edge.Replaces(a, o) if o == n.id => a
      case Edge.Replaces(a, o) if a == n.id => o
    }.distinct
