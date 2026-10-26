package frflow.project.pipeline

import frflow.core.analysis.{Choice, Resolve, Resolved, Valid}
import frflow.core.name.NodeId
import frflow.decision.review.{Reading, Standing, Subjects}
import frflow.proof.layout.LeanProject
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, ObligationName, Obligations}
import frflow.proof.reading.ProofRules
import frflow.proof.terms.TermTable

/** The pure state of a project: every phase after elaboration, each computed once, on demand. */
final class Analysis(val valid: Valid, val inputs: Inputs, val computed: Computed):
  lazy val decided: Resolved = Resolve(valid, Choice.Decided(accepted))
  lazy val provisional: Resolved = Resolve(valid, Choice.FirstListed)
  lazy val terms: TermTable = TermTable.of(decided)
  lazy val obligations: List[NodeObligations] = Obligations.of(decided, terms, authored, computed.evaluations)
  lazy val modules: List[LeanModule] = LeanProject.of(decided, terms, obligations)
  lazy val subjects: Subjects = ReadSubjects(this)
  lazy val reading: Reading = Reading(subjects, inputs.ledger)
  lazy val standings: Map[NodeId, Standing] = reading.standings

  def withRecorded(r: Recorded): Analysis = Analysis(valid, inputs.copy(recorded = r), computed)

  private def accepted: Set[NodeId] = inputs.ledger.decisions.keySet.filter(inputs.ledger.binding(_).isDefined)
  private def authored: Set[(NodeId, ObligationName)] =
    inputs.proofs.toSet.flatMap((id, f) => ProofRules.theorems(f).map(id -> _))
