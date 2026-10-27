package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, Obligation}
import frflow.proof.terms.TermTable

/** The Lean of a knowledge base: every module, from the resolved theory and its obligations. Pure; `project` writes
  * the files (and only those that changed) and runs Lean on them.
  */
object LeanProject:
  def of(r: Resolved, table: TermTable, obligations: List[NodeObligations], whole: List[Obligation])
      : List[LeanModule] =
    VocabularyModules.of(r) ++ obligations.flatMap(NodeModules.of(r, table, _)) ++ RootImplModule.of(r, table).toList ++
      Option.when(whole.nonEmpty)(WholeModule.of(r, table, whole)).toList
