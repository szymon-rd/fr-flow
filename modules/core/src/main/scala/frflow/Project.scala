package frflow

import frflow.check.ProofAuditor
import frflow.dsl
import frflow.lint.{LintIssue, Lints}
import frflow.model.*
import frflow.obligation.Obligation
import frflow.render.{LeanRenderer, Nodes}
import frflow.workspace.{Files2, Hashing, Workspace}
import java.nio.file.Files

/** Facts about the FrFlow kernel the generated code depends on. */
object Kernel:
  val toolchain: String = "leanprover/lean4:v4.35.0"
  val defaultAllowedAxioms: Set[String] = Set("propext", "Classical.choice", "Quot.sound")

/** Content hashes of a node (the theory or a layer).
  *
  * @param spec  what a human approves: statement, rationale, the Scala sources
  *              of the node and the Lean they translate to, cited assumptions
  * @param check everything verification depends on: spec, obligations,
  *              automation, assembly, authored proofs, the parent's check hash
  *              and the kernel sources
  */
final case class NodeHashes(spec: String, check: String)

/** A model bound to a workspace on disk. */
final class Project(val theory: TheoryModel, val ws: Workspace):

  def this(model: dsl.Model, ws: Workspace) = this(TheoryModel.from(model), ws)

  val TheoryId: String = Nodes.TheoryId

  /** Obligations with an authored proof, per node, read from the proof files. */
  def authored: Map[String, Set[String]] =
    val base = LeanRenderer(theory)
    base.nodeIds.flatMap { id =>
      Files2.read(ws.lean(base.proofsPath(id))).map { src =>
        val names = base.obligations(id).map(_.name).toSet
        id -> ProofAuditor.declarations(src).map(_.name).filter(names).toSet
      }
    }.toMap

  /** The renderer, aware of which obligations have authored proofs. */
  def renderer: LeanRenderer = LeanRenderer(theory, authored)

  def lint(): Seq[LintIssue] = Lints.run(theory)

  def nodeIds: List[String] = renderer.nodeIds
  def obligations(id: String): List[Obligation] = renderer.obligations(id)

  /** Parent node in verification order: layers wait for their parent layer. */
  def parentNode(id: String): Option[String] =
    if id == TheoryId then None else theory.layerOrFail(id).parent

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

    val r = renderer
    val files = r.renderAll
    val written = files.toSeq.sortBy(_._1).collect {
      case (rel, content) if Files2.writeIfChanged(ws.lean(rel), content) => rel
    }
    val keep = files.keySet.map(ws.lean(_).normalize())
    val removed = r.generatedDirs.flatMap(d => Files2.listFiles(ws.lean(d))).filterNot(p => keep(p.normalize()))
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

  /** What a human reviews for a node: Scala sources and the Lean they become. */
  def specText(id: String): String =
    val r = renderer
    if id == TheoryId then
      val defs = theory.theoryDefs.map(n => sourceOf(n) + "\n" + r.renderDef(n))
      val laws = theory.laws.map(l => s"${l.name}|${l.statement}|${l.lifted.source}")
      val assumptions = theory.assumptions.map(a => s"${a.id}|${a.name}|${a.statement}|${a.justification}")
      (Seq(theory.name) ++ defs ++ laws ++ assumptions).mkString("\u0000")
    else
      val l = theory.layerOrFail(id)
      val defs = theory.layerDefs(l).map(n => r.renderDef(n))
      val used = l.assumptionsUsed.sorted.flatMap(theory.assumption).map(a => s"${a.id}|${a.statement}|${a.justification}")
      (Seq(l.id, l.name, l.kind.label, l.statement, l.rationale, r.renderModel(l)) ++ l.lifted.map(_.source) ++ defs ++ used)
        .mkString("\u0000")

  private def sourceOf(name: String): String =
    theory.defs.adts.get(name).map(_.source).orElse(theory.defs.funs.get(name).map(_.source)).getOrElse("")

  def hashes: Map[String, NodeHashes] =
    val r = renderer
    nodeIds.foldLeft(Map.empty[String, NodeHashes]) { (acc, id) =>
      val spec = Hashing.sha256(specText(id))
      val proofs = Files2.read(ws.lean(r.proofsPath(id))).getOrElse("")
      val parentCheck = parentNode(id).flatMap(acc.get).map(_.check).getOrElse("")
      val generated =
        if id == TheoryId then Seq(r.renderDomain, r.renderTheoryObligations, r.renderAuto(id), r.renderTheoryAssembly)
        else
          val l = theory.layerOrFail(id)
          Seq(r.renderDomain, r.renderObligations(l), r.renderAuto(id), r.renderAssembly(l))
      val check = Hashing.sha256((Seq(spec) ++ generated ++ Seq(proofs, parentCheck, kernelHash)).mkString("\u0000"))
      acc.updated(id, NodeHashes(spec, check))
    }

  // ---------------------------------------------------------------------------
  // Authored proof files
  // ---------------------------------------------------------------------------

  /** Creates the proof file of a node or appends stubs for `names` that have no
    * theorem yet. Never modifies existing theorems. Returns the added names.
    */
  def scaffold(id: String, names: Seq[String]): Seq[String] =
    val r = renderer
    val path = ws.lean(r.proofsPath(id))
    val existing = Files2.read(path)
    val declared = existing.toSeq.flatMap(src => ProofAuditor.declarations(src).map(_.name)).toSet
    val missing = r.obligations(id).filter(o => names.contains(o.name) && !declared(o.name))
    if missing.isEmpty then Nil
    else
      val stubs = missing.map(r.proofStub).mkString
      val footer = r.proofFileFooter(id)
      val content = existing match
        case None => r.proofFileHeader(id) + stubs + footer
        case Some(src) =>
          val idx = src.lastIndexOf(footer.trim)
          if idx >= 0 then src.substring(0, idx) + stubs + src.substring(idx)
          else src + "\n" + stubs
      Files2.writeIfChanged(path, content)
      missing.map(_.name)
