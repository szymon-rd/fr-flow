package frflow.project.pipeline

import frflow.core.analysis.{Resolve, Resolved, Valid}
import frflow.core.consistency.{Consistency, Group}
import frflow.core.expr.OutsideFact
import frflow.core.checking.Checking
import frflow.core.name.{ModelName, NodeId}
import frflow.decision.content.CodeNow
import frflow.decision.review.{Reading, Standing, Subjects}
import frflow.project.code.{CodeFingerprints, Governance}
import frflow.proof.layout.{Layout, LeanProject, Lowering, RootImplModule}
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{Discharge, NodeObligations, Obligation, ObligationName, Obligations}
import frflow.proof.reading.{ProofFile, ProofRules}
import frflow.proof.terms.TermTable
import frflow.proof.verdict.{CheckKey, NodeCheck, WholeCheck}
import frflow.proof.whole.{ExampleGoals, Joint, Possible}
import frflow.testing.model.ModelRuns
import frflow.testing.report.TestReport

/** The pure state of a project: every phase after elaboration, each computed once, on demand. */
final class Analysis(val valid: Valid, val inputs: Inputs, val computed: Computed):
  lazy val decided: Resolved = Resolve(valid)
  lazy val terms: TermTable = TermTable.of(decided)
  lazy val obligations: List[NodeObligations] = Obligations.of(decided, terms, authored)
  /** What is asked of the theory as a whole: consistency and vacuity, with the witnesses found, and the examples; each
    * the developer's proof file (`Proofs/<Model>/Whole.lean`) proves, authored (owner §39).
    */
  lazy val whole: List[Obligation] =
    (Joint.of(decided) ++ Possible.of(decided, computed.found) ++ ExampleGoals.of(decided, computed.examples.map(_._1)))
      .map(o => if wholeProven(o.name) then o.copy(discharge = Discharge.Authored) else o)
  /** The developer's proof file of the theory's own obligations, if there is one. */
  lazy val wholeProof: Option[ProofFile] = inputs.lean.proofs.collectFirst {
    case (id, f) if Layout(decided.theory.name).proofs(id) == Layout(decided.theory.name).wholeProofs => f
  }
  private lazy val wholeProven: Set[ObligationName] = wholeProof.toList.flatMap(ProofRules.theorems).toSet
  /** The consistency groups by their index, as `consistent_<i>` names them. */
  lazy val groups: List[(Int, List[NodeId])] =
    Consistency.of(decided.theory).zipWithIndex.collect { case (Group.Sharing(ids, _, _, _, _), i) => i -> ids }
  lazy val lowering: Lowering = Lowering(decided, terms)
  /** The lowering a node's content prints what its formula means with (`Contents`): variables named by order. */
  lazy val canonical: Lowering = Lowering(decided, terms, canonical = true)
  lazy val modules: List[LeanModule] = LeanProject.of(decided, terms, obligations, whole)
  /** The roots `root_impl` is asked of. */
  lazy val rooted: Set[NodeId] = RootImplModule.roots(lowering).toSet
  lazy val keys: CheckKeys = CheckKeys(decided.theory.name, modules, inputs.lean, rooted)
  private lazy val nodeKeys: Map[NodeId, CheckKey] = obligations.map(o => o.node -> keys.node(o.node)).toMap
  /** Each node's governed code now: the files it governs, fingerprinted. */
  lazy val governed: Map[NodeId, CodeNow] = Governance.of(decided.theory, inputs.sources.keys.toList).map((id, fs) =>
    id -> CodeFingerprints.of(fs.map(f => f -> inputs.sources.get(f.path))))
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
  /** The models whose operations' Scala, tested against the model, a node rests on (owner §36): each its checking
    * says it rests on (`TestedOnModel`), and of the assumption that only the code changes a model's state, that model.
    */
  def models(id: NodeId): List[ModelName] =
    val t = decided.theory
    (Checking.of(t, id).collect { case Checking.TestedOnModel(m, _) => m } ++
      t.node(id).flatMap(_.statement.outside).collect { case OutsideFact.OnlyCodeChanges(m) => m })
      .filter(t.code.implemented.contains).distinct
  /** What a test report recorded under `id` is of: the nodes resting on a model's Scala, for a model's runs
    * (`ModelRuns.reportedUnder`); the node itself otherwise.
    */
  def reportedFor(id: NodeId): List[NodeId] =
    val t = decided.theory
    t.code.implemented.keys.find(ModelRuns.reportedUnder(_) == id)
      .fold(List(id))(m => t.nodes.map(_.node.id).filter(models(_).contains(m)))
  /** A model's operations' Scala's report, by the model, while current. */
  def testedModel(m: ModelName): Option[TestReport] = tested(ModelRuns.reportedUnder(m))

  def withRecorded(r: Recorded): Analysis = Analysis(valid, inputs.copy(recorded = r), computed)

  private def authored: Set[(NodeId, ObligationName)] =
    inputs.lean.proofs.toSet.flatMap((id, f) => ProofRules.theorems(f).map(id -> _))
