package frflow.project.pipeline

import frflow.core.analysis.{Resolve, Resolved, Valid}
import frflow.core.consistency.{Consistency, Group}
import frflow.core.name.NodeId
import frflow.decision.review.{Reading, Standing, Subjects}
import frflow.proof.layout.LeanProject
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, Obligation, ObligationName, Obligations}
import frflow.proof.whole.{ExampleGoals, Joint, Possible}
import frflow.proof.reading.ProofRules
import frflow.proof.terms.TermTable

/** The pure state of a project: every phase after elaboration, each computed once, on demand. */
final class Analysis(val valid: Valid, val inputs: Inputs, val computed: Computed):
  lazy val decided: Resolved = Resolve(valid)
  lazy val terms: TermTable = TermTable.of(decided)
  lazy val obligations: List[NodeObligations] = Obligations.of(decided, terms, authored)
  /** What is asked of the theory as a whole: consistency and vacuity, with the witnesses found, and the examples. */
  lazy val whole: List[Obligation] =
    Joint.of(decided) ++ Possible.of(decided, computed.found) ++
      ExampleGoals.of(decided, computed.examples.map(_._1))
  /** The consistency groups by their index, as `consistent_<i>` names them. */
  lazy val groups: List[(Int, List[NodeId])] =
    Consistency.of(decided.theory).zipWithIndex.collect { case (Group.Sharing(ids, _, _, _), i) => i -> ids }
  lazy val modules: List[LeanModule] = LeanProject.of(decided, terms, obligations, whole)
  lazy val subjects: Subjects = ReadSubjects(this)
  lazy val reading: Reading = Reading(subjects, inputs.ledger)
  lazy val standings: Map[NodeId, Standing] = reading.standings

  def withRecorded(r: Recorded): Analysis = Analysis(valid, inputs.copy(recorded = r), computed)

  private def authored: Set[(NodeId, ObligationName)] =
    inputs.proofs.toSet.flatMap((id, f) => ProofRules.theorems(f).map(id -> _))
