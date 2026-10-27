package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.proof.terms.TermTable

/** What Lean is asked of each node (docs/DAG.md §3): a function of the resolved theory and of the obligations the
  * proof files prove. What is asked of the theory as a whole is `Joint`'s and `ExampleGoals`'.
  */
object Obligations:
  def of(r: Resolved, table: TermTable, authored: Set[(NodeId, ObligationName)]): List[NodeObligations] =
    r.theory.refinement.nodes.filter(_.statement.stated).map { n =>
      NodeObligations(n.id, Required.of(r, authored, n.id), Tries.of(r, table, n.id))
    }
