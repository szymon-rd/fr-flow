package frflow.project.pipeline

import frflow.core.name.{KbName, NodeId}
import frflow.decision.content.Sha
import frflow.proof.layout.Layout
import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.print.Print
import frflow.proof.reading.ProofFile
import frflow.proof.verdict.CheckKey

/** What a check depends on: every Lean file it builds (a root's `root_impl` among them, `rooted`), and every file
  * those import, however far (the generated modules' text, the proof files'), with the checker's version, Lean's
  * toolchain and FrFlow's Lean library's version. A change
  * to any of them checks it again; nothing else does (a statement reworded but meaning the same in Lean does not).
  */
final class CheckKeys(kb: KbName, modules: List[LeanModule], lean: LeanSources, rooted: Set[NodeId]):
  private val layout = Layout(kb)
  private val generated: Map[String, LeanModule] = modules.map(m => m.name.dotted -> m).toMap
  private val authored: Map[String, ProofFile] =
    lean.proofs.map((id, f) => layout.proofs(id).dotted -> f)
  private lazy val printed: Map[String, String] = generated.map((n, m) => n -> Print.module(m))

  /** A node's: its own modules, its proof file, and what they import. */
  def node(id: NodeId): CheckKey =
    val prefix = s"FrFlowGen.${kb.value}.${id.value}."
    val own = generated.keys.filter(n => n.startsWith(prefix) && n != layout.refutes(id).dotted).toList ++
      authored.keys.filter(_ == layout.proofs(id).dotted) ++
      Option.when(rooted(id))(layout.rootImpl.dotted)
    key(own)

  /** The theory's own: `Whole.lean`, the examples tried beside it, the audit of the developer's proofs of it (so their
    * proof file), and what they import.
    */
  lazy val whole: CheckKey =
    key(List(layout.wholeSpec, layout.whole, layout.wholeChecks, layout.wholeAudit).map(_.dotted)
      .filter(generated.contains))

  private def key(start: List[String]): CheckKey =
    val read = closure(start.distinct.sorted)
    CheckKey(Sha.parts((CheckKeys.Version.toString :: LeanSources.Toolchain :: lean.library ::
      read.flatMap(n => List(n, text(n))))*))

  /** Each module named, then each it imports not seen yet, sorted. */
  private def closure(start: List[String]): List[String] =
    frflow.core.graph.Walk.breadthFirst(start, identity)(n => imports(n)).sorted

  private def text(n: String): String =
    printed.get(n).orElse(authored.get(n).map(_.source)).getOrElse("<missing>")

  private def imports(n: String): List[String] = generated.get(n).fold(
    authored.get(n).toList.flatMap(f => CheckKeys.Imported.findAllMatchIn(f.source).map(_.group(1)).toList))(
    _.imports.map(_.dotted))

object CheckKeys:
  /** How checks are made and read: a change to it checks every node again. */
  val Version: Int = 1
  private val Imported = """(?m)^\s*import\s+(\S+)""".r

