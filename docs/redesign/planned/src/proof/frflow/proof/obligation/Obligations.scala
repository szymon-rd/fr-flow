package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.proof.terms.TermTable

/** What Lean is asked of each node (docs/DAG.md §3): a function of the resolved theory, of the obligations the proof
  * files prove, and of what Scala computed of the examples and probes.
  */
object Obligations:
  def of(r: Resolved, table: TermTable, authored: Set[(NodeId, ObligationName)],
      evaluated: Map[NodeId, List[Evaluation]]): List[NodeObligations] =
    r.theory.refinement.nodes.filter(_.statement.stated).map { n =>
      NodeObligations(n.id, Required.of(r, authored, n.id), Tries.of(r, table, n.id), evaluated.getOrElse(n.id, Nil))
    }
