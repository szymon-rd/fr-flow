package frflow

import java.nio.charset.StandardCharsets.UTF_8
import frflow.Json.*
import java.nio.file.{Files, Path, StandardOpenOption}
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
  def snapshotFile: Path = root.resolve(".frflow/kb.json")
  def eventsFile: Path = root.resolve(".frflow/events.jsonl")

/** The FrFlow workflow on one knowledge base: render, check, approve, report. */
final class Workflow(val kb: KnowledgeBase, val ws: Workspace):

  private def read(p: Path): Option[String] = if Files.isRegularFile(p) then Some(Files.readString(p, UTF_8)) else None
  private def write(p: Path, s: String): Boolean =
    if read(p).contains(s) then false
    else { Files.createDirectories(p.getParent); Files.writeString(p, s, UTF_8); true }
  private def sha(parts: String*): String =
    MessageDigest.getInstance("SHA-256").digest(parts.mkString("\u0000").getBytes(UTF_8)).map("%02x".format(_)).mkString

  def idea: String = read(ws.root.resolve(kb.idea)).getOrElse("")
  def ledger: Ledger = Ledger.load(ws.ledgerFile)

  /** Nodes whose obligation has an authored proof. */
  def authored: Set[String] =
    val base = Generate(kb)
    kb.nodes.filter(n => read(ws.lean.resolve(base.proofsPath(n.id))).exists(src => Lean.theorems(src).exists(_.name == "link")))
      .map(_.id).toSet

  def generate: Generate = Generate(kb, authored)

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
  // Hashes: what the developer approves, and what a check depends on
  // ---------------------------------------------------------------------------

  private lazy val kernelHash: String =
    val dir = ws.lean.resolve(ws.kernelPath).normalize.resolve("FrFlow")
    val files = if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.toList.sortBy(_.toString) else Nil
    sha(files.flatMap(read)*)

  /** What the developer reviews: statement, Scala sources, the Lean they become, and the idea for the root. */
  def specHash(n: Node[?]): String =
    val g = generate
    sha((Seq(n.id, n.statement, g.spec(n)) ++ g.declarationsUsedBy(n) ++ n.lifted.map(_.source) ++ n.substs.map(s => s"${s.name}:=${s.lean}") ++
      (if n.kind == NodeKind.Root then Seq(idea) else Nil))*)

  def checkHash(n: Node[?]): String =
    val g = generate
    sha(specHash(n), g.auto(n), g.theorems(n), read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse(""),
      n.parent.fold("")(checkHash), kernelHash)

  // ---------------------------------------------------------------------------
  // Check
  // ---------------------------------------------------------------------------

  /** Checks nodes (all, or one), parents first, and records the results in the ledger. */
  def check(only: Option[String] = None): List[(Node[?], NodeCheck)] =
    render()
    val lake = Lake(ws.lean)
    val g = generate
    val results = kb.ordered.filter(n => only.forall(_ == n.id)).foldLeft(List.empty[(Node[?], NodeCheck)]) { (acc, n) =>
      val parentStatus = n.parent.map(p => acc.find(_._1 eq p).map(_._2.status).orElse(current(p).map(_.status)).getOrElse("not-checked"))
      acc :+ (n -> checkNode(n, g, lake, parentStatus))
    }
    Ledger.save(ws.ledgerFile, results.foldLeft(ledger)((l, r) => l.updated(r._1.id)(_.copy(check = Some(r._2)))))
    results.foreach((n, c) => record("check", n.id, "status" -> str(c.status)))
    results

  private def checkNode(n: Node[?], g: Generate, lake: Lake, parentStatus: Option[String]): NodeCheck =
    def done(status: String, rs: List[Result], msgs: List[String], axioms: List[String] = Nil) =
      NodeCheck(checkHash(n), status, rs, msgs, axioms, java.time.Instant.now.toString)
    def errors(r: Run) =
      val ds = Lean.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
      if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))

    val spec = lake.build(g.specModule(n.id))
    if !spec.ok then return done("model-error", Nil, errors(spec))

    val results = g.obligation(n).toList.map { o =>
      val rel = if authored(n.id) then g.proofsPath(n.id) else g.autoPath(n.id)
      val src = read(ws.lean.resolve(rel)).getOrElse("")
      val run = lake.elaborate(rel)
      val diags = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
      Lean.theorems(src).find(_.name == o.name) match
        case None => Result(o.name, "open", s"no theorem ${o.name} in $rel")
        case Some(d) =>
          def in(l: Int) = l >= d.from && l <= d.to
          val bad = Lean.violations(src).filter(v => in(v._1))
          if d.statement != s"Obl.${o.name}" then Result(o.name, "failed", s"must state exactly Obl.${o.name}")
          else if bad.nonEmpty then Result(o.name, "failed", s"forbidden: ${bad.map(_._2).mkString(", ")}")
          else diags.find(x => x.isError && in(x.line)) match
            case Some(err) => Result(o.name, "open", err.message.linesIterator.next().take(300))
            case None if diags.exists(x => x.isSorry && in(x.line)) => Result(o.name, "open", "uses sorry")
            case None if !run.ok => Result(o.name, "open", "not checked: " + run.output.take(300))
            case None => Result(o.name, "proven", if authored(n.id) then "authored" else "auto")
    }
    if results.exists(_.status == "failed") then return done("failed", results, Nil)
    if results.exists(_.status == "open") then
      return done("open", results, List(s"prove it in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)"))
    if parentStatus.exists(_ != "proven") then return done("waiting", results, List(s"waiting for ${n.parent.get.id}"))

    val thms = lake.build(g.theoremsModule(n.id))
    if !thms.ok then return done("failed", results, "the node's theorems do not build" :: errors(thms))
    val ax = Lean.axioms(lake.elaborate(g.auditPath(n.id)).output)
    val used = g.auditedTheorems(n).flatMap(t => ax.getOrElse(t, List("<no audit result>"))).distinct.sorted
    val extra = used.filterNot(Lean.allowedAxioms)
    if extra.nonEmpty then done("failed", results, List(s"disallowed axioms: ${extra.mkString(", ")}"), used)
    else done("proven", results, Nil, used)

  /** The recorded check of a node, if still current. */
  def current(n: Node[?]): Option[NodeCheck] = ledger.entry(n.id).check.filter(_.hash == checkHash(n))

  // ---------------------------------------------------------------------------
  // Approve, scaffold, report
  // ---------------------------------------------------------------------------

  def approve(n: Node[?], by: String): Unit =
    Ledger.save(ws.ledgerFile, ledger.updated(n.id)(_.copy(approval = Some(Approval(specHash(n), by, java.time.Instant.now.toString)))))
    record("approve", n.id, "by" -> str(by))

  /** Creates the proof file of a node with a stub for its obligation. */
  def scaffold(n: Node[?]): Boolean =
    val g = generate
    val path = ws.lean.resolve(g.proofsPath(n.id))
    if g.obligation(n).isEmpty || Files.exists(path) then false
    else
      record("scaffold", n.id)
      write(path, g.proofFile(n))

  def approvalState(n: Node[?]): String = ledger.entry(n.id).approval match
    case None                             => "unapproved"
    case Some(a) if a.hash == specHash(n) => "approved"
    case Some(_)                          => "changed"

  def verification(n: Node[?]): String = ledger.entry(n.id).check match
    case None                              => "not-checked"
    case Some(c) if c.hash != checkHash(n) => "stale"
    case Some(c)                           => c.status

  def tree(mark: Option[String] = None): String =
    def go(n: Node[?], depth: Int): List[String] =
      val here = if mark.contains(n.id) then "   ← this node" else ""
      s"${"  " * depth}${n.id} (${n.kind.toString.toLowerCase})  [${approvalState(n)}, ${verification(n)}]$here" ::
        kb.children(n).flatMap(go(_, depth + 1))
    go(kb.root, 0).mkString("\n")

  def status: String =
    val ok = kb.nodes.forall(n => approvalState(n) == "approved" && verification(n) == "proven")
    tree() + "\n\n" + (if ok then "Every node is approved and proven." else "Not every node is approved and proven.") + "\n"

  /** Everything needed to work on a node: the idea, the path from the root, and the node's state. */
  def context(n: Node[?]): String =
    val g = generate
    val sb = StringBuilder()
    sb ++= s"# ${kb.name} / ${n.id}\n\n## Idea\n\n${idea.trim}\n\n## Knowledge base\n\n```\n${tree(Some(n.id))}\n```\n\n"
    sb ++= "## Path from the root\n\n"
    kb.path(n).foreach { a =>
      sb ++= s"### ${a.id} (${a.kind.toString.toLowerCase})\n\n${a.statement}\n\n"
      def code(label: String, l: Lifted[?]) = sb ++= s"$label:\n```scala\n${l.source}\n```\n"
      a.spec.foreach(code("spec", _))
      a.abs.foreach(code("abs", _))
      a.post.foreach(code("post", _))
      a.substs.foreach(s => sb ++= s"- `${s.name} := ${s.term.fold(s.lean)(_.source)}`\n")
      sb ++= "\n"
    }
    g.obligation(n).foreach { o =>
      val st = current(n).flatMap(_.obligations.headOption).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail})" else ""}")
      sb ++= s"## Obligation of ${n.id} [$st]\n\n${o.description}\n\n```lean\n${o.statement}\n```\n\n"
    }
    sb ++= s"""## Rules
       |
       |- The model is the Scala code. Change it there; the Lean in `lean/FrFlowGen` is generated.
       |- If `frflow_auto` does not prove an obligation, prove it in `lean/${g.proofsPath(n.id)}`, stating exactly `Obl.link`.
       |- If an obligation is false, the node is wrong: fix it, or propose a change to it.
       |- A node is accepted when it is proven and the developer has approved it.
       |""".stripMargin
    sb.result()

  // ---------------------------------------------------------------------------
  // Snapshot and event log: what the browser and agents read
  // ---------------------------------------------------------------------------

  /** Appends an event to `.frflow/events.jsonl`: the history of the process. */
  def record(action: String, node: String, fields: (String, Json)*): Unit =
    Files.createDirectories(ws.eventsFile.getParent)
    val e = obj((Seq("at" -> str(java.time.Instant.now.toString), "action" -> str(action), "node" -> str(node)) ++ fields)*)
    Files.writeString(ws.eventsFile, e.compact + "\n", UTF_8, StandardOpenOption.CREATE, StandardOpenOption.APPEND)

  /** The state of a node's link to its parent: `proven` (by `auto`, `authored`, or `instantiation`),
    * `open`, `failed`, `not-checked` or `stale`. None for the root.
    */
  def link(n: Node[?]): Json =
    def st(status: String, detail: String) = obj("status" -> str(status), "detail" -> str(detail))
    if n.parent.isEmpty then JNull
    else
      current(n) match
        case None => st(verification(n), "")
        case Some(c) => c.obligations.headOption match
          case Some(r) => st(r.status, r.detail)
          case None if c.status == "model-error" => st("failed", "the model does not build")
          case None => st(if c.status == "failed" then "failed" else "proven", "instantiation")

  /** The knowledge base as data, built from the Scala definitions and the ledger. */
  def snapshot: Json =
    val g = generate
    def strs(xs: Seq[String]) = JArr(xs.map(str))
    def node(n: Node[?]): Json =
      val check = current(n)
      val approval = ledger.entry(n.id).approval
      obj(
        "id" -> str(n.id),
        "kind" -> str(n.kind.toString.toLowerCase),
        "statement" -> str(n.statement),
        "parent" -> n.parent.fold(JNull)(p => str(p.id)),
        "sources" -> JObj(Seq("spec" -> n.spec, "abs" -> n.abs, "post" -> n.post).collect { case (k, Some(l)) => k -> str(l.source) }),
        "substitutions" -> JArr(n.substs.map(s => obj("name" -> str(s.name), "value" -> str(s.term.fold(s.lean)(_.source))))),
        "obligation" -> g.obligation(n).fold(JNull)(o => obj("statement" -> str(o.statement), "description" -> str(o.description))),
        "link" -> link(n),
        "proof" -> read(ws.lean.resolve(g.proofsPath(n.id))).fold(JNull)(src => obj("file" -> str("lean/" + g.proofsPath(n.id)), "source" -> str(src))),
        "rootTheorem" -> str(g.rootTheorem(n)),
        "lean" -> str(g.spec(n)),
        "approval" -> str(approvalState(n)),
        "approvedBy" -> approval.fold(JNull)(a => str(a.by)),
        "verification" -> str(verification(n)),
        "messages" -> strs(check.toList.flatMap(_.messages)),
        "axioms" -> strs(check.toList.flatMap(_.axioms))
      )
    obj(
      "name" -> str(kb.name),
      "idea" -> str(idea),
      "root" -> str(kb.root.id),
      "exportedAt" -> str(java.time.Instant.now.toString),
      "opaques" -> strs(kb.nodes.flatMap(_.lifted).flatMap(_.opaques).distinct),
      "params" -> JArr(kb.params.map(p => obj(
        "name" -> str(p.name),
        "type" -> str(kb.nodes.flatMap(_.lifted).flatMap(_.paramRefs).toMap.getOrElse(p.name, "")),
        "assumption" -> p.assumption.fold(JNull)(a => str(a.source))
      ))),
      "types" -> JArr(kb.types.map(t => obj("name" -> str(t.name), "lean" -> str(t.lean)))),
      "defs" -> JArr(kb.defs.map(d => obj("name" -> str(d.name), "source" -> str(d.lifted.source)))),
      "nodes" -> JArr(kb.ordered.map(node))
    )

  /** Writes the snapshot to `.frflow/kb.json`. */
  def writeSnapshot(): Path =
    Files.createDirectories(ws.snapshotFile.getParent)
    Files.writeString(ws.snapshotFile, snapshot.render() + "\n", UTF_8)
    ws.snapshotFile
