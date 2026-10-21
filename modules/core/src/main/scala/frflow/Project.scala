package frflow

import frflow.lint.{LintIssue, Lints}
import frflow.model.*
import frflow.render.LeanRenderer
import frflow.workspace.{Files2, Hashing, Workspace}
import java.nio.file.Files

/** Facts about the FrFlow kernel the generated code depends on. */
object Kernel:
  val toolchain: String = "leanprover/lean4:v4.35.0"
  val defaultAllowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")

/** Content hashes of a node.
  *
  * @param spec  statement, rationale, assumptions used and rendered model:
  *              what a human approves
  * @param check everything verification depends on: spec, obligations, assembly,
  *              proof file, the parent's check hash and the kernel sources
  */
final case class NodeHashes(spec: String, check: String)

/** A theory bound to a workspace on disk. */
final class Project(val theory: TheoryModel, val ws: Workspace):
  val renderer = LeanRenderer(theory)

  def lint(): Seq[LintIssue] = Lints.run(theory)

  // ---------------------------------------------------------------------------
  // Rendering
  // ---------------------------------------------------------------------------

  final case class RenderResult(written: Seq[String], removed: Seq[String], created: Seq[String])

  def render(): RenderResult =
    val created = Seq.newBuilder[String]
    if !Files.exists(ws.lean("lakefile.toml")) then
      Files2.writeIfChanged(ws.lean("lakefile.toml"), lakefile)
      created += "lakefile.toml"
    if !Files.exists(ws.lean("lean-toolchain")) then
      Files2.writeIfChanged(ws.lean("lean-toolchain"), Kernel.toolchain + "\n")
      created += "lean-toolchain"

    val files = renderer.renderAll
    val written = files.toSeq.sortBy(_._1).collect {
      case (rel, content) if Files2.writeIfChanged(ws.lean(rel), content) => rel
    }
    val keep = files.keySet.map(ws.lean(_).normalize())
    val removed = renderer.generatedDirs.flatMap(d => Files2.listFiles(ws.lean(d))).filterNot(p => keep(p.normalize()))
    removed.foreach(Files.delete)
    RenderResult(written, removed.map(p => ws.leanDir.relativize(p).toString), created.result())

  def lakefile: String =
    s"""name = "${theory.name.toLowerCase}"
       |defaultTargets = ["FrFlowGen"]
       |
       |[[require]]
       |name = "frflow"
       |path = "${ws.kernelPath}"
       |
       |[[lean_lib]]
       |name = "Proofs"
       |globs = ["Proofs.+"]
       |
       |[[lean_lib]]
       |name = "FrFlowGen"
       |globs = ["FrFlowGen.+"]
       |""".stripMargin

  // ---------------------------------------------------------------------------
  // Hashes
  // ---------------------------------------------------------------------------

  private lazy val kernelHash: String =
    val kernelDir = ws.leanDir.resolve(ws.kernelPath).normalize()
    val sources = Files2.listFiles(kernelDir).filter(_.toString.endsWith(".lean"))
      .filterNot(_.toString.contains("/.lake/")).sortBy(_.toString)
    Hashing.sha256(sources.map(p => Files2.read(p).getOrElse("")).mkString("\u0000"))

  def hashes: Map[String, NodeHashes] =
    theory.topological.foldLeft(Map.empty[String, NodeHashes]) { (acc, n) =>
      val usedAssumptions = n.spec.events.flatMap(_.assumes.map(_.assumptionId)).distinct.sorted
        .flatMap(theory.assumption).map(a => s"${a.id}|${a.statement}|${a.justification}")
      val spec = Hashing.sha256(
        Seq(n.id, n.name, n.statement, n.rationale, renderer.renderModel(n), usedAssumptions.mkString("\n"))
          .mkString("\u0000")
      )
      val proofs = Files2.read(ws.lean(renderer.proofsPath(n))).getOrElse("")
      val parentCheck = n.parent.flatMap(acc.get).map(_.check).getOrElse("")
      val check = Hashing.sha256(
        Seq(spec, renderer.renderObligations(n), renderer.renderAssembly(n), proofs, parentCheck, kernelHash)
          .mkString("\u0000")
      )
      acc.updated(n.id, NodeHashes(spec, check))
    }

  // ---------------------------------------------------------------------------
  // Proof scaffolding
  // ---------------------------------------------------------------------------

  /** Creates the proof file of a node, or appends stubs for obligations that
    * have no theorem yet. Never modifies existing theorems. Returns added names.
    */
  def scaffold(n: Node): Seq[String] =
    val path = ws.lean(renderer.proofsPath(n))
    val existing = Files2.read(path)
    val declared = existing.toSeq.flatMap(src => check.ProofAuditor.declarations(src).map(_.name)).toSet
    val missing = renderer.obligations(n).filterNot(o => declared(o.name))
    if missing.isEmpty && existing.isDefined then Nil
    else
      val stubs = missing.map(renderer.proofStub).mkString
      val footer = renderer.proofFileFooter(n)
      val content = existing match
        case None => renderer.proofFileHeader(n) + stubs + footer
        case Some(src) =>
          val idx = src.lastIndexOf(footer.trim)
          if idx >= 0 then src.substring(0, idx) + stubs + src.substring(idx)
          else src + "\n" + stubs
      Files2.writeIfChanged(path, content)
      missing.map(_.name)
