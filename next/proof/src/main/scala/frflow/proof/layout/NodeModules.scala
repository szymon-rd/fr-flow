package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.NodeObligations
import frflow.proof.terms.TermTable

/** The modules of one node, from its obligations. */
object NodeModules:
  def of(r: Resolved, table: TermTable, o: NodeObligations): List[LeanModule] = ???
