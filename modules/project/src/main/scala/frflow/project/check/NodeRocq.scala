package frflow.project.check

import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis
import frflow.proof.layout.{Layout, NodePart, Refutation, RefutesModule}
import frflow.proof.lean.ast.{LeanModule, ModuleName}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.{Constant, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, ProofFile, RocqReport, RocqSource}
import frflow.proof.rocq.RocqProject
import frflow.proof.verdict.ProverRun
import frflow.testing.search.Refuted

/** One node's Rocq as its check reads it: its modules, its obligations by where each is proven, its proof file and
  * the lemmas it imports, and what Rocq said of a module it built.
  */
final class NodeRocq(a: Analysis, val node: NodeId):
  val layout: Layout = Layout(a.decided.theory.name)
  private val asked = a.obligations.find(_.node == node)

  def module(part: NodePart): ModuleName = layout.ofNode(node, part)
  def has(part: NodePart): Boolean = a.modules.exists(_.name == module(part))

  def required(name: ObligationName): Option[Obligation] = asked.flatMap(_.required.find(_.name == name))
  /** What the checks module proves: every obligation but `complete` and `impl`. */
  def others: List[Obligation] = asked.toList.flatMap(_.required).filterNot(o =>
    o.name == ObligationName.Complete || o.name == ObligationName.Impl)
  def tried: List[Obligation] = asked.toList.flatMap(_.tried)
  def named(o: Obligation): String = LowerObligation.name(o.name).text
  def rooted: Boolean = a.rooted(node)

  def proof: Option[ProofFile] = a.inputs.proofs.files.get(node)
  /** The shared lemmas, when its proof file imports them. */
  def lemmas: Option[ProofFile] =
    proof.filter(f => RocqSource.imports(f.source).contains(RocqProject.logical(layout.lemmas)))
      .flatMap(_ => a.inputs.proofs.files.get(NodeId("Lemmas")))

  /** Its step refuted on the case found (`Refutations`), as Rocq is given it: the module, and its text; none of a
    * case Rocq is not printed.
    */
  def refutes(r: Refuted): Option[(LeanModule, String)] =
    val found = Refutation(r.witness, r.ty, r.inputs.zip(r.types).map((x, ty) => Constant(x._2, ty)))
    val m = RefutesModule.of(a.decided, a.terms, node, found)
    RocqProject(a.modules :+ m).text(m.name).map(m -> _)

  /** What Rocq said of a module of the node it ran on; none of one it did not run (a module it imports did not go
    * through), so nothing in it is judged.
    */
  def elaborated(part: NodePart, r: ProverRun): Option[Elaboration] = NodeRocq.generated(a, module(part), r)
  def elaboratedRoot(r: ProverRun): Option[Elaboration] = NodeRocq.generated(a, layout.rootImpl, r)
  def elaboratedProof(r: ProverRun): Option[Elaboration] = proof.flatMap(f =>
    NodeRocq.said(layout.proofs(node), f.source, List(layout.kb.value, node.value, "Proofs"), r))

object NodeRocq:
  /** What Rocq said of a generated module it ran on. */
  def generated(a: Analysis, m: ModuleName, r: ProverRun): Option[Elaboration] =
    a.modules.find(_.name == m).flatMap(module => a.rocq.text(m).flatMap(said(module, _, r)))

  def said(m: LeanModule, source: String, r: ProverRun): Option[Elaboration] =
    said(m.name, source, m.namespace.map(_.text), r)

  /** What Rocq said of a module with this text, its lemmas named in `namespace`; none when the build's report has
    * nothing of its file: Rocq did not run on it.
    */
  def said(m: ModuleName, source: String, namespace: List[String], r: ProverRun): Option[Elaboration] =
    val file = RocqProject.file(m)
    Option.when(RocqReport.read(output(r)).exists(_.path == file))(Elaboration(source, output(r), file, namespace))

  def output(r: ProverRun): String = r match
    case ProverRun.Built(o)    => o
    case ProverRun.Failed(o)   => o
    case ProverRun.TimedOut(o) => o
