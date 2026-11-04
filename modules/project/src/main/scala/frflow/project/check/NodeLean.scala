package frflow.project.check

import frflow.core.name.NodeId
import frflow.eval.Races
import frflow.project.pipeline.Analysis
import frflow.proof.layout.{Layout, NodePart, Refutation, RefutesModule}
import frflow.proof.lean.ast.{LeanModule, ModuleName}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.Print
import frflow.proof.obligation.{Constant, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, ProofFile}
import frflow.proof.verdict.ProverRun
import frflow.testing.search.Refuted

/** One node's Lean as its check reads it: its modules, its obligations by where each is proven, its proof file and
  * the lemmas it imports, and what Lean said of a module it built.
  */
final class NodeLean(a: Analysis, val node: NodeId):
  val layout: Layout = Layout(a.decided.theory.name)
  private val asked = a.obligations.find(_.node == node)

  def module(part: NodePart): ModuleName = layout.ofNode(node, part)
  def has(part: NodePart): Boolean = a.modules.exists(_.name == module(part))
  def text(part: NodePart): String = a.modules.find(_.name == module(part)).fold("")(Print.module)

  def required(name: ObligationName): Option[Obligation] = asked.flatMap(_.required.find(_.name == name))
  /** What the checks module proves: every obligation but `complete` and `impl`. */
  def others: List[Obligation] = asked.toList.flatMap(_.required).filterNot(o =>
    o.name == ObligationName.Complete || o.name == ObligationName.Impl)
  def tried: List[Obligation] = asked.toList.flatMap(_.tried)
  def named(o: Obligation): String = LowerObligation.name(o.name).text
  def rooted: Boolean = a.rooted(node)

  def proof: Option[ProofFile] = a.inputs.lean.proofs.get(node)
  def proofText: String = proof.fold("")(_.source)
  /** The shared lemmas, when its proof file imports them. */
  def lemmas: Option[ProofFile] = proof.filter(f => s"(?m)^\\s*import\\s+${layout.lemmas.dotted}\\b".r
    .findFirstIn(f.source).isDefined).flatMap(_ => a.inputs.lean.proofs.get(NodeId("Lemmas")))

  /** Its step refuted on the case found (`Refutations`), as Lean is given it. */
  def refutes(r: Refuted): LeanModule =
    val found = Refutation(r.witness, r.ty, r.inputs.zip(r.types).map((x, ty) => Constant(Races.without(x._2), ty)))
    RefutesModule.of(a.decided, a.terms, node, found)

  def file(m: ModuleName): String = m.file.value.stripPrefix("lean/")

  /** What Lean said of a module of the node it built; none when Lake did not run Lean on it (a module it imports
    * failed), so nothing in it is judged.
    */
  def elaborated(part: NodePart, r: ProverRun): Option[Elaboration] = said(module(part), text(part), r)
  def elaborated(m: LeanModule, r: ProverRun): Option[Elaboration] = said(m.name, Print.module(m), r)
  def elaboratedRoot(r: ProverRun): Option[Elaboration] =
    said(layout.rootImpl, a.modules.find(_.name == layout.rootImpl).fold("")(Print.module), r)
  def elaboratedProof(r: ProverRun): Option[Elaboration] = said(layout.proofs(node), proofText, r)

  private def said(m: ModuleName, source: String, r: ProverRun): Option[Elaboration] =
    Option.when(NodeLean.ran(m, r))(Elaboration(source, NodeLean.output(r), file(m)))

object NodeLean:
  /** Whether Lake ran Lean on `m`: the build went through, or Lake's output has a line of `m`'s job (a module whose
    * import failed has none).
    */
  def ran(m: ModuleName, r: ProverRun): Boolean = r match
    case ProverRun.Built(_) => true
    case other              =>
      val job = s"""^[✔ℹ✖⚠].*\\s${java.util.regex.Pattern.quote(m.dotted)}(\\s.*)?$$""".r
      output(other).linesIterator.exists(job.matches)

  def output(r: ProverRun): String = r match
    case ProverRun.Built(o)    => o
    case ProverRun.Failed(o)   => o
    case ProverRun.TimedOut(o) => o
