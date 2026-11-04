package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.proof.audit.Audit
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, Obligation}
import frflow.proof.terms.TermTable

/** The Lean of a FrModel: every module, from the resolved theory and its obligations, each audited (`Audit`: a FrFlow
  * bug if a term built is ill-formed or an obligation the theory asks is missing). Pure; `project` writes the files
  * (and only those that changed) and runs Lean on them.
  */
object LeanProject:
  def of(r: Resolved, table: TermTable, obligations: List[NodeObligations], whole: List[Obligation])
      : List[LeanModule] =
    val l = Lowering(r, table)
    Audit.checked(r, obligations.flatMap(o => o.required ++ o.tried) ++ whole, VocabularyModules.of(l) ++
      obligations.flatMap(NodeModules.of(l, _)) ++ RootImplModule.of(l).toList ++
      (if whole.isEmpty then Nil else WholeModule.of(l, whole)) ++ WholeModule.checks(l, whole).toList ++
      WholeModule.audit(l, whole).toList)
