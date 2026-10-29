package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, Obligation}
import frflow.proof.terms.TermTable

/** The Lean of a FrModel: every module, from the resolved theory and its obligations. Pure; `project` writes
  * the files (and only those that changed) and runs Lean on them.
  */
object LeanProject:
  def of(r: Resolved, table: TermTable, obligations: List[NodeObligations], whole: List[Obligation])
      : List[LeanModule] =
    val l = Lowering(r, table)
    VocabularyModules.of(l) ++ obligations.flatMap(NodeModules.of(l, _)) ++ RootImplModule.of(l).toList ++
      (if whole.isEmpty then Nil else WholeModule.of(l, whole)) ++ WholeModule.checks(l, whole).toList ++
      WholeModule.audit(l, whole).toList
