package frflow.project.pipeline

import frflow.core.analysis.resolution.{Resolve, Resolved, Valid}
import frflow.core.consistency.{Consistency, Group}
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.content.CodeNow
import frflow.decision.review.{Reading, Standing, Subjects}
import frflow.eval.run.Broken
import frflow.project.code.{CodeFingerprints, Governance, ModelFiles}
import frflow.proof.audit.LeanProject
import frflow.proof.audit.Obligations
import frflow.proof.layout.{Layout, Lowering, RootImplModule}
import frflow.proof.lean.ast.LeanModule
import frflow.proof.obligation.{Discharge, NodeObligations, Obligation, ObligationName}
import frflow.proof.reading.{ProofFile, ProofRules}
import frflow.proof.terms.TermTable
import frflow.proof.verdict.{CheckKey, NodeCheck, WholeCheck}
import frflow.proof.whole.{ExampleGoals, Joint, Possible}
import frflow.testing.report.{Failure, TestReport}

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
  /** The consistency groups by their index, as `consistent_<i>` names them: of premises, with every group taking
    * them, which rests on them.
    */
  lazy val groups: List[(Int, List[NodeId])] =
    val all = Consistency.of(decided.theory).zipWithIndex
    all.collect {
      case (Group.Sharing(ids, _, _, _, _), i) => i -> ids
      case (Group.Premises(ps, _, _), i)       => i -> (ps ++ all.collect {
          case (Group.Sharing(ids, _, _, _, qs), _) if qs.exists(ps.contains) => ids
        }.flatten).distinct
    }
  lazy val lowering: Lowering = Lowering(decided, terms)
  /** The lowering a node's content prints what its formula means with (`Contents`): variables named by order. */
  lazy val canonical: Lowering = Lowering(decided, terms, canonical = true)
  lazy val modules: List[LeanModule] = LeanProject.of(decided, terms, obligations, whole)
  /** The roots `root_impl` is asked of. */
  lazy val rooted: Set[NodeId] = RootImplModule.roots(lowering).toSet
  lazy val keys: CheckKeys = CheckKeys(decided.theory.name, modules, inputs.lean, rooted)
  private lazy val nodeKeys: Map[NodeId, CheckKey] = obligations.map(o => o.node -> keys.node(o.node)).toMap
  /** Each node's governed code now: the files it governs, fingerprinted. */
  lazy val governed: Map[NodeId, CodeNow] = Governance.of(decided.theory, inputs.sources.keys.toList, own)
    .map((id, fs) => id -> CodeFingerprints.of(fs.map(f => f -> inputs.sources.get(f.path))))
  /** The files of the model's own (owner §38), and those that need no node to govern them (`ModelFiles`). */
  lazy val own: Set[RelPath] = ModelFiles.own(decided.theory, inputs.sources)
  lazy val accounted: Set[RelPath] = ModelFiles.accounted(decided.theory, inputs.sources)
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
  /** The rules a current test report found a value breaking (`Broken.Always`), on whichever node's code the value
    * was made or handed: tested plain Scala making it.
    */
  lazy val broken: Set[NodeId] = currentTests.values.flatMap(_.failure).collect {
    case Failure(_, _, Broken.Always(rule), _) => rule
  }.toSet
  private lazy val currentTests: Map[NodeId, TestReport] =
    inputs.recorded.tests.collect { case (id, (k, r)) if k == TestKeys.of(this, id) => id -> r }
  def withRecorded(r: Recorded): Analysis = Analysis(valid, inputs.copy(recorded = r), computed)

  private def authored: Set[(NodeId, ObligationName)] =
    inputs.lean.proofs.toSet.flatMap((id, f) => ProofRules.theorems(f).map(id -> _))
