package frflow.project.pipeline

import frflow.core.analysis.{Resolve, Resolved, Valid}
import frflow.core.consistency.{Consistency, Group}
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.decision.content.CodeNow
import frflow.decision.review.{Reading, Standing, Subjects}
import frflow.project.code.{CodeFingerprints, Governance}
import frflow.proof.layout.{LeanProject, Lowering, RootImplModule}
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{NodeObligations, Obligation, ObligationName, Obligations}
import frflow.proof.reading.ProofRules
import frflow.proof.terms.TermTable
import frflow.proof.verdict.{CheckKey, NodeCheck, WholeCheck}
import frflow.proof.whole.{ExampleGoals, Joint, Possible}
import frflow.testing.report.TestReport

/** The pure state of a project: every phase after elaboration, each computed once, on demand. */
final class Analysis(val valid: Valid, val inputs: Inputs, val computed: Computed):
  lazy val decided: Resolved = Resolve(valid)
  lazy val terms: TermTable = TermTable.of(decided)
  lazy val obligations: List[NodeObligations] = Obligations.of(decided, terms, authored)
  /** What is asked of the theory as a whole: consistency and vacuity, with the witnesses found, and the examples. */
  lazy val whole: List[Obligation] =
    Joint.of(decided) ++ Possible.of(decided, computed.found) ++ ExampleGoals.of(decided, computed.examples.map(_._1))
  /** The consistency groups by their index, as `consistent_<i>` names them. */
  lazy val groups: List[(Int, List[NodeId])] =
    Consistency.of(decided.theory).zipWithIndex.collect { case (Group.Sharing(ids, _, _, _), i) => i -> ids }
  lazy val lowering: Lowering = Lowering(decided, terms)
  lazy val modules: List[LeanModule] = LeanProject.of(decided, terms, obligations, whole)
  /** The roots `root_impl` is asked of. */
  lazy val rooted: Set[NodeId] = RootImplModule.roots(lowering).toSet
  lazy val keys: CheckKeys = CheckKeys(decided.theory.name, modules, inputs.proofs, rooted)
  private lazy val nodeKeys: Map[NodeId, CheckKey] = obligations.map(o => o.node -> keys.node(o.node)).toMap
  /** Each node's governed code now: the files it governs, fingerprinted. */
  lazy val governed: Map[NodeId, CodeNow] = Governance.of(decided.theory, inputs.sources.keys.toList).map((id, fs) =>
    id -> CodeFingerprints.of(fs.map(f => f -> inputs.sources.get(f))))
  lazy val subjects: Subjects = ReadSubjects(this)
  lazy val reading: Reading = Reading(subjects, inputs.ledger.counting)
  lazy val standings: Map[NodeId, Standing] = reading.standings

  /** Its recorded check, while its key is the node's now. */
  def current(id: NodeId): Option[NodeCheck] =
    inputs.recorded.checks.nodes.get(id).filter(c => nodeKeys.get(id).contains(c.key))
  /** The theory's recorded check, while its key is the theory's now. */
  def wholeCheck: Option[WholeCheck] = inputs.recorded.checks.whole.filter(_.key == keys.whole)
  /** Its recorded test report, while its key is the node's now. */
  def tested(id: NodeId): Option[TestReport] = currentTests.get(id)
  private lazy val currentTests: Map[NodeId, TestReport] =
    inputs.recorded.tests.collect { case (id, (k, r)) if k == TestKeys.of(this, id) => id -> r }
  /** A store said to behave as its model, with implementations to test against it (attached, or tested before). */
  def modelled(id: NodeId): Boolean = decided.theory.node(id).flatMap(_.statement.outside).exists {
    case OutsideFact.BehavesAs(b, _) => decided.theory.code.realized.contains(b) || inputs.recorded.tests.contains(id)
    case _                           => false
  }

  def withRecorded(r: Recorded): Analysis = Analysis(valid, inputs.copy(recorded = r), computed)

  private def authored: Set[(NodeId, ObligationName)] =
    inputs.proofs.toSet.flatMap((id, f) => ProofRules.theorems(f).map(id -> _))
