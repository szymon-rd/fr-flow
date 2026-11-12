package frflow.project.pipeline

import frflow.core.graph.Walk
import frflow.core.name.{KbName, NodeId}
import frflow.decision.content.Sha
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.reading.RocqSource
import frflow.proof.rocq.RocqProject
import frflow.proof.verdict.CheckKey

/** What a check depends on: every Rocq file it builds (a root's `root_impl` among them, `rooted`), and every file
  * those import, however far (the generated modules' text, the proof files'), with the checker's version and
  * FrFlow's Rocq library's version. A change to any of them checks it again; nothing else does (a statement reworded
  * but meaning the same in Rocq does not).
  */
final class CheckKeys(kb: KbName, rocq: RocqProject, proofs: ProofSources, rooted: Set[NodeId]):
  private val layout = Layout(kb)
  /** Each module's text, by the name Rocq loads it by: the generated modules', the proof files'. */
  private val texts: Map[String, String] =
    rocq.files.map((file, text) => file.stripSuffix(".v").replace('/', '.') -> text).toMap ++
      proofs.files.map((id, f) => RocqProject.logical(layout.proofs(id)) -> f.source)

  /** A node's: its own modules, its proof file, and what they import. */
  def node(id: NodeId): CheckKey =
    val prefix = RocqProject.logical(layout.ofNode(id, NodePart.Spec)).stripSuffix(NodePart.Spec.toString)
    val own = texts.keys.filter(n => n.startsWith(prefix) && n != RocqProject.logical(layout.refutes(id))).toList ++
      Some(RocqProject.logical(layout.proofs(id))).filter(texts.contains) ++
      Option.when(rooted(id))(RocqProject.logical(layout.rootImpl))
    key(own)

  /** The theory's own: `Whole.v`, the examples tried beside it, the audit of the developer's proofs of it (so their
    * proof file), and what they import.
    */
  lazy val whole: CheckKey =
    key(List(layout.wholeSpec, layout.whole, layout.wholeChecks, layout.wholeAudit).map(RocqProject.logical)
      .filter(texts.contains))

  /** Each module named, then each it imports not seen yet, sorted; of one that is neither generated nor a proof file
    * (the library's, Rocq's own), its name alone.
    */
  private def key(start: List[String]): CheckKey =
    val read = Walk.breadthFirst(start.distinct.sorted, identity)(n =>
      texts.get(n).toList.flatMap(RocqSource.imports)).sorted
    CheckKey(Sha.parts((CheckKeys.Version.toString :: proofs.library ::
      read.flatMap(n => List(n, texts.getOrElse(n, ""))))*))

object CheckKeys:
  /** How checks are made and read: a change to it checks every node again (4: the prover is Rocq). */
  val Version: Int = 4
