package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule
import frflow.proof.terms.TermTable

/** `RootImpl.lean`: `root_impl`, composed from every node's `holds` and every proven implementation. */
object RootImplModule:
  def of(r: Resolved, table: TermTable): Option[LeanModule] = ???
