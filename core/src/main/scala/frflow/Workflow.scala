package frflow

import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import java.security.MessageDigest
import scala.jdk.CollectionConverters.*

/** Where a project lives on disk.
  *
  * {{{
  * <root>/IDEA.md               the developer's idea (the project's `idea` file)
  * <root>/lean/                 Lean workspace: FrFlowGen/ (generated), Proofs/ (authored)
  * <root>/.frflow/ledger.json   approvals and check results
  * }}}
  *
  * @param kernelPath path of the FrFlow Lean kernel, relative to `lean/`
  */
final case class Workspace(root: Path, kernelPath: String):
  def lean: Path = root.resolve("lean")
  def ledgerFile: Path = root.resolve(".frflow/ledger.json")

/** The FrFlow workflow on one project: render, check, approve, report. */
final class Workflow(val project: Project, val ws: Workspace):

  private def read(p: Path): Option[String] = if Files.isRegularFile(p) then Some(Files.readString(p, UTF_8)) else None
  private def write(p: Path, s: String): Boolean =
    if read(p).contains(s) then false
    else { Files.createDirectories(p.getParent); Files.writeString(p, s, UTF_8); true }
  private def sha(parts: String*): String =
    MessageDigest.getInstance("SHA-256").digest(parts.mkString("\u0000").getBytes(UTF_8)).map("%02x".format(_)).mkString

  def idea: String = read(ws.root.resolve(project.idea)).getOrElse("")
  def ledger: Ledger = Ledger.load(ws.ledgerFile)

  /** Obligations with an authored proof, read from the proof files. */
  def authored: Map[String, Set[String]] =
    val base = Generate(project)
    project.nodes.flatMap { n =>
      read(ws.lean.resolve(base.proofsPath(n.id))).map { src =>
        n.id -> Lean.theorems(src).map(_.name).filter(base.obligations(n).map(_.name).contains).toSet
      }
    }.toMap

  def generate: Generate = Generate(project, authored)

  // ---------------------------------------------------------------------------
  // Render
  // ---------------------------------------------------------------------------

  /** Writes the generated Lean; returns the files that changed. */
  def render(): List[String] =
    val g = generate
    write(ws.lean.resolve("lakefile.toml"), g.lakefile(ws.kernelPath))
    write(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
    val files = g.files
    val changed = files.toList.sortBy(_._1).collect { case (rel, text) if write(ws.lean.resolve(rel), text) => rel }
    val keep = files.keySet.map(ws.lean.resolve(_).normalize)
    g.generatedDirs.map(ws.lean.resolve).filter(Files.isDirectory(_)).foreach { d =>
      Files.walk(d).iterator.asScala.toList.filter(Files.isRegularFile(_)).filterNot(p => keep(p.normalize)).foreach(Files.delete)
    }
    changed

  // ---------------------------------------------------------------------------
  // Hashes: what a developer approves, and what a check depends on
  // ---------------------------------------------------------------------------

  private lazy val kernelHash: String =
    val dir = ws.lean.resolve(ws.kernelPath).normalize.resolve("FrFlow")
    val files = if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.toList.sortBy(_.toString) else Nil
    sha(files.flatMap(read)*)

  /** Hash of what the developer reviews: statement, Scala sources, scenarios, the Lean they become, and the idea for the root. */
  def specHash(n: Node[?, ?]): String =
    val g = generate
    sha((Seq(n.id, n.statement, g.spec(n), g.types) ++ n.lifted.map(_.source) ++ n.scenarios.map(_.toString) ++
      (if n.isRoot then Seq(idea) else Nil))*)

  def checkHash(n: Node[?, ?]): String =
    val g = generate
    val parent = project.parentOf(n).fold("")(checkHash)
    sha(specHash(n), g.auto(n), g.theorems(n), read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse(""), parent, kernelHash)

  // ---------------------------------------------------------------------------
  // Check
  // ---------------------------------------------------------------------------

  /** Runs the scenarios of a node on its Scala predicates. */
  def scenarios[S, E](n: Node[S, E]): List[Result] = n.scenarios.map { sc =>
    try
      val states = sc.start :: sc.steps.map(_._2)
      val firstFailure =
        if !n.init.value(sc.start) then Some("the start state is not initial")
        else sc.steps.zip(states).zipWithIndex.collectFirst {
          case (((e, t), s), i) if !n.next.value(s, e, t) => s"step ${i + 1} ($e) is not allowed"
        }
      (sc.expectAllowed, firstFailure) match
        case (true, None)       => Result(sc.name, "ok", "allowed, as expected")
        case (true, Some(why))  => Result(sc.name, "failed", s"expected to be allowed, but $why")
        case (false, Some(why)) => Result(sc.name, "ok", s"forbidden, as expected: $why")
        case (false, None)      => Result(sc.name, "failed", "expected to be forbidden, but the node allows it")
    catch case e: NotExecutable => Result(sc.name, "failed", s"cannot be evaluated: ${e.getMessage}")
  }

  /** Checks nodes (all, or one), parents first, and records the results in the ledger. */
  def check(only: Option[String] = None): List[(Node[?, ?], NodeCheck)] =
    render()
    val lake = Lake(ws.lean)
    val g = generate
    val results = project.ordered.filter(n => only.forall(_ == n.id)).foldLeft(List.empty[(Node[?, ?], NodeCheck)]) { (acc, n) =>
      val parentStatus = project.parentOf(n).map(p => acc.find(_._1 eq p).map(_._2.status).orElse(current(p).map(_.status)).getOrElse("not-checked"))
      acc :+ (n -> checkNode(n, g, lake, parentStatus))
    }
    val updated = results.foldLeft(ledger)((l, r) => l.updated(r._1.id)(_.copy(check = Some(r._2))))
    Ledger.save(ws.ledgerFile, updated)
    results

  private def checkNode(n: Node[?, ?], g: Generate, lake: Lake, parentStatus: Option[String]): NodeCheck =
    val now = java.time.Instant.now.toString
    val sc = scenarios(n)
    val obls = g.obligations(n)
    def done(status: String, rs: List[Result], msgs: List[String], axioms: List[String] = Nil) =
      NodeCheck(checkHash(n), status, rs, sc, msgs, axioms, now)

    val spec = lake.build(g.specModule(n.id))
    if !spec.ok then
      return done("model-error", obls.map(o => Result(o.name, "open", "the model does not type-check")),
        Lean.diagnostics(spec.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}"))

    def attribute(rel: String, names: Set[String]): Map[String, Result] =
      read(ws.lean.resolve(rel)).fold(Map.empty) { src =>
        val run = lake.elaborate(rel)
        val diags = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
        val bad = Lean.violations(src)
        Lean.theorems(src).filter(d => names(d.name)).map { d =>
          def in(l: Int) = l >= d.from && l <= d.to
          val r =
            if d.statement != s"Obl.${d.name}" then Result(d.name, "failed", s"must state exactly Obl.${d.name}")
            else if bad.exists(v => in(v._1)) then Result(d.name, "failed", s"forbidden: ${bad.filter(v => in(v._1)).map(_._2).mkString(", ")}")
            else diags.find(x => x.isError && in(x.line)) match
              case Some(err) => Result(d.name, "open", err.message.linesIterator.next().take(300))
              case None if diags.exists(x => x.isSorry && in(x.line)) => Result(d.name, "open", "uses sorry")
              case None if !run.ok && !diags.exists(_.isError) => Result(d.name, "open", "not checked: " + run.output.take(200))
              case None => Result(d.name, "proven", if rel.startsWith("Proofs") then "authored" else "auto")
          d.name -> r
        }.toMap
      }

    val names = obls.map(_.name).toSet
    val auto = attribute(g.autoPath(n.id), names)
    val proofs = attribute(g.proofsPath(n.id), names)
    val rs = obls.map(o => proofs.get(o.name).orElse(auto.get(o.name)).getOrElse(Result(o.name, "open", "no proof")))

    val scenarioFailures = sc.filter(_.status != "ok").map(r => s"scenario ${r.name}: ${r.detail}")
    if rs.exists(_.status == "failed") || scenarioFailures.nonEmpty then return done("failed", rs, scenarioFailures)
    if rs.exists(_.status == "open") then
      return done("open", rs, List(s"open obligations need a proof in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)"))
    if parentStatus.exists(_ != "proven") then return done("waiting", rs, List(s"waiting for ${project.parentOf(n).get.id} to be proven"))

    val thms = lake.build(g.theoremsModule(n.id))
    if !thms.ok then
      return done("failed", rs, "the proofs do not compose into the node's theorems" ::
        Lean.diagnostics(thms.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}"))
    val ax = Lean.axioms(lake.elaborate(g.auditPath(n.id)).output)
    val used = g.auditedTheorems(n).flatMap(t => ax.getOrElse(t, List("<no audit result>"))).distinct.sorted
    val extra = used.filterNot(Lean.allowedAxioms)
    if extra.nonEmpty then done("failed", rs, List(s"disallowed axioms: ${extra.mkString(", ")}"), used)
    else done("proven", rs, Nil, used)

  /** The recorded check of a node, if it is still current. */
  def current(n: Node[?, ?]): Option[NodeCheck] = ledger.entry(n.id).check.filter(_.hash == checkHash(n))

  // ---------------------------------------------------------------------------
  // Approve, scaffold, report
  // ---------------------------------------------------------------------------

  def approve(n: Node[?, ?], by: String): Unit =
    Ledger.save(ws.ledgerFile, ledger.updated(n.id)(_.copy(approval = Some(Approval(specHash(n), by, java.time.Instant.now.toString)))))

  /** Adds proof stubs for obligations that are not proven (or for all). Returns the names added. */
  def scaffold(n: Node[?, ?], all: Boolean = false): List[String] =
    val g = generate
    val path = ws.lean.resolve(g.proofsPath(n.id))
    val existing = read(path)
    val have = existing.toList.flatMap(src => Lean.theorems(src).map(_.name)).toSet
    val wanted =
      if all then g.obligations(n).map(_.name)
      else current(n).toList.flatMap(_.obligations).filter(_.status != "proven").map(_.name)
    val names = wanted.filterNot(have)
    if names.nonEmpty then write(path, g.proofFile(n, names, existing))
    names

  def approvalState(n: Node[?, ?]): String = ledger.entry(n.id).approval match
    case None                                 => "unapproved"
    case Some(a) if a.hash == specHash(n)     => "approved"
    case Some(_)                              => "changed"

  def verification(n: Node[?, ?]): String =
    ledger.entry(n.id).check match
      case None                                => "not-checked"
      case Some(c) if c.hash != checkHash(n)   => "stale"
      case Some(c)                             => c.status

  def tree(mark: Option[String] = None): String =
    def go(n: Node[?, ?], depth: Int): List[String] =
      val here = if mark.contains(n.id) then "   ← this node" else ""
      s"${"  " * depth}${n.id}  [${approvalState(n)}, ${verification(n)}]$here" :: project.children(n).flatMap(go(_, depth + 1))
    go(project.root, 0).mkString("\n")

  def status: String =
    val ok = project.nodes.forall(n => approvalState(n) == "approved" && verification(n) == "proven")
    tree() + "\n\n" + (if ok then "Every node is approved and proven." else "Not every node is approved and proven.") + "\n"

  /** Everything needed to work on a node: the idea, the path from the root, and the node's state. */
  def context(n: Node[?, ?]): String =
    val g = generate
    val sb = StringBuilder()
    sb ++= s"# ${project.name} / ${n.id}\n\n## Idea\n\n${idea.trim}\n\n## Knowledge base\n\n```\n${tree(Some(n.id))}\n```\n\n"
    sb ++= "## Path from the root\n\n"
    project.path(n).foreach { a =>
      sb ++= s"### ${a.id}\n\n${a.statement}\n\n"
      def code(label: String, l: Lifted[?]) = sb ++= s"$label:\n```scala\n${l.source}\n```\n"
      code("init", a.init)
      code("next", a.next)
      code(if a.isRoot then "theorem" else "property", a.property)
      a.parent.foreach { l => code("abs", l.abs); code("event", l.event) }
      if a.scenarios.nonEmpty then
        sb ++= "\nscenarios:\n" + a.scenarios.map(s => s"- ${if s.expectAllowed then "allowed" else "forbidden"}: ${s.name}").mkString("\n") + "\n"
      sb ++= "\n"
    }
    val results = current(n).map(_.obligations.map(r => r.name -> r).toMap).getOrElse(Map.empty)
    sb ++= s"## Obligations of ${n.id}\n\n"
    g.obligations(n).foreach { o =>
      val st = results.get(o.name).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail})" else ""}")
      sb ++= s"- `${o.name}` [$st]: ${o.description}\n  `${o.statement}`\n"
    }
    sb ++= s"""
       |## Rules
       |
       |- The model is the Scala code. Change it there; the Lean in `lean/FrFlowGen` is generated.
       |- Prove an obligation `frflow_auto` leaves open in `lean/${g.proofsPath(n.id)}`, stating exactly `Obl.<name>`.
       |- If an obligation or a scenario fails, the node is wrong: fix the node, or propose a change to it.
       |- A node is accepted when it is proven and the developer has approved it.
       |""".stripMargin
    sb.result()
