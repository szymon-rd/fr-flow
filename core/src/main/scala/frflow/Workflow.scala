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
  * <root>/.frflow/ledger.json   the developer's decisions (committed)
  * <root>/.frflow/checks.json   check results (derived, not committed)
  * }}}
  *
  * @param kernelPath path of the FrFlow Lean kernel, relative to `lean/`
  */
final case class Workspace(root: Path, kernelPath: String):
  def lean: Path = root.resolve("lean")
  def ledgerFile: Path = root.resolve(".frflow/ledger.json")
  def checksFile: Path = root.resolve(".frflow/checks.json")
  def snapshotFile: Path = root.resolve(".frflow/kb.json")
  def requestsFile: Path = root.resolve(".frflow/requests.json")

/** The FrFlow workflow on one knowledge base: render, check, decide, report. */
final class Workflow(val kb: KnowledgeBase, val ws: Workspace):

  private def read(p: Path): Option[String] = if Files.isRegularFile(p) then Some(Files.readString(p, UTF_8)) else None
  private def write(p: Path, s: String): Boolean =
    if read(p).contains(s) then false
    else { Files.createDirectories(p.getParent); Files.writeString(p, s, UTF_8); true }
  private def sha(parts: String*): String =
    MessageDigest.getInstance("SHA-256").digest(parts.mkString("\u0000").getBytes(UTF_8)).map("%02x".format(_)).mkString

  def idea: String = read(ws.root.resolve(kb.idea)).getOrElse("")
  def ledger: Ledger = Ledger.load(ws.ledgerFile)
  def checks: Map[String, NodeCheck] = Checks.load(ws.checksFile)

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
  // Content: what the developer decides; hashes
  // ---------------------------------------------------------------------------

  private lazy val kernelHash: String =
    val dir = ws.lean.resolve(ws.kernelPath).normalize.resolve("FrFlow")
    val files = if Files.isDirectory(dir) then Files.list(dir).iterator.asScala.toList.sortBy(_.toString) else Nil
    sha(files.flatMap(read)*)

  /** The idea a root is decided against: IDEA.md without its `## Not modelled` section. */
  def ideaDecided: String = Decisions.splitIdea(idea)._1

  /** The `## Not modelled` section of IDEA.md: the limits of the theory. */
  def notModelled: String = Decisions.splitIdea(idea)._2

  /** The open terms a node relies on, with what they mean in the world. */
  def vocabulary(n: Node[?]): List[String] =
    val named = n.substs.map(_.name).toSet
    val used = n.lifted ++ n.lifted.flatMap(_.defs).map(_.lifted)
    val opaques = (used.flatMap(_.opaqueObjects) ++ kb.opaques.filter(o => named(o.name))).distinctBy(_.name)
    val params = (used.flatMap(_.paramObjects) ++ kb.params.filter(p => named(p.name))).distinctBy(_.name)
    (opaques.map(o => s"${o.name}: ${o.means}") ++ params.map(p => s"${p.name}: ${p.means}")).sorted

  /** The terms a node is the first on its path to use: their meaning is decided there, and reaches
    * the nodes below through the chain.
    */
  def introduced(n: Node[?]): List[String] =
    val above = kb.path(n).dropRight(1).flatMap(vocabulary).map(_.takeWhile(_ != ':')).toSet
    vocabulary(n).filterNot(t => above(t.takeWhile(_ != ':')))

  /** The node as the developer sees it and decides it. A decision is bound to its hash. */
  def content(n: Node[?]): Json = JObj(Seq(
    "parent" -> n.parent.fold(JNull)(p => str(p.id)),
    "statement" -> str(n.statement),
    "why" -> str(n.why),
    "sources" -> JObj(Seq("spec" -> n.spec, "abs" -> n.abs, "post" -> n.post).collect { case (k, Some(l)) => k -> str(l.source) }),
    "substitutions" -> JArr(n.substs.map(s => str(s"${s.name} := ${s.term.fold(s.lean)(_.source)}"))),
    "examples" -> JArr(n.cases.map(e => str(e.describe))),
    "vocabulary" -> JArr(introduced(n).map(str)),
    "uses" -> JArr(generate.declarationsUsedBy(n).map(str)),
    "governs" -> JArr(n.governs.map(str))
  ) ++ kb.implementation(n).filter(_.wiring.nonEmpty).map(i => "implementation" -> str(i.wiring)).toList
    ++ (if n.kind == NodeKind.Root then Seq("idea" -> str(ideaDecided), "notModelled" -> str(notModelled)) else Nil))

  def hash(n: Node[?]): String = Decision.hash(content(n))

  /** The node's content together with its ancestors': a change anywhere above shows below.
    * What is not modelled is reviewed at the roots only: it narrows no node below them.
    */
  def chainHash(n: Node[?]): String =
    Decisions.chain(content(n), n.parent.fold("")(chainHash))

  /** Files governed explicitly by some node. */
  private lazy val governedExplicitly: Set[Path] =
    kb.nodes.flatMap(_.governs).map(f => ws.root.resolve(f).toAbsolutePath.normalize).toSet

  /** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. */
  def checkHash(n: Node[?]): String =
    val g = generate
    sha((Seq(g.spec(n), g.auto(n), g.theorems(n), g.vacuity(n).getOrElse(""), g.unsatFile(n).getOrElse(""), read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse(""),
      n.parent.fold("")(checkHash), kernelHash) ++ g.declarationsUsedBy(n))*)

  // ---------------------------------------------------------------------------
  // Check
  // ---------------------------------------------------------------------------

  /** Checks nodes (all, or one), parents first, and records the results. */
  def check(only: Option[String] = None): List[(Node[?], NodeCheck)] =
    render()
    val lake = Lake(ws.lean)
    val g = generate
    val results = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id)).foldLeft(List.empty[(Node[?], NodeCheck)]) { (acc, n) =>
      val parentStatus = n.parent.map(p => acc.find(_._1 eq p).map(_._2.status).orElse(current(p).map(_.status)).getOrElse("not-checked"))
      // A node whose formal parts did not change keeps its result.
      val c = current(n).filter(_ => only.isEmpty).getOrElse(checkNode(n, g, lake, parentStatus))
      acc :+ (n -> c)
    }
    val kept = checks.filter((id, _) => kb.node(id).isDefined)
    Checks.save(ws.checksFile, results.foldLeft(kept)((m, r) => m.updated(r._1.id, r._2)))
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
          val bad = if authored(n.id) then Lean.violations(src) else Nil
          if d.statement != s"Obl.${o.name}" then Result(o.name, "failed", s"must state exactly Obl.${o.name}")
          else if bad.nonEmpty then Result(o.name, "failed", s"not allowed in a proof file: ${bad.map(_._2).distinct.mkString(", ")}")
          else diags.find(x => x.isError && in(x.line)) match
            case Some(err) => Result(o.name, "open", err.message.linesIterator.next().take(300))
            case None if diags.exists(x => x.isSorry && in(x.line)) => Result(o.name, "open", "uses sorry")
            case None if !run.ok => Result(o.name, "open", "not checked: " + run.output.take(300))
            case None => Result(o.name, "proven", if authored(n.id) then "authored" else "auto")
    }
    if results.exists(_.status == "failed") then return done("failed", results, Nil)
    if results.exists(_.status == "open") then
      return done("open", results, List(s"prove it in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)"))
    // A link that holds whatever the node says proves nothing; a node no model meets says nothing.
    if g.vacuity(n).isDefined && lake.elaborate(g.vacuityPath(n.id)).ok then
      return done("failed", results.map(_.copy(status = "failed", detail = s"vacuous: ${n.parent.get.id} holds whatever ${n.id} says")),
        List(s"the link proves nothing: every model of ${n.id} meets ${n.parent.get.id}, whatever its spec"))
    if g.unsatFile(n).isDefined && lake.elaborate(g.unsatPath(n.id)).ok then
      return done("failed", results.map(_.copy(status = "failed", detail = s"unsatisfiable: no model meets ${n.id}")),
        List(s"${n.id} is contradictory: no model meets it, so every link below it holds and says nothing"))
    if parentStatus.exists(_ != "proven") then return done("waiting", results, List(s"waiting for ${n.parent.get.id}"))

    val thms = lake.build(g.theoremsModule(n.id))
    if !thms.ok then return done("failed", results, "the node's theorems do not build" :: errors(thms))
    // Replay the authored proof through the kernel, so nothing elaborated around it is trusted.
    if authored(n.id) then
      val replay = lake.replay(g.proofsModule(n.id))
      if !replay.ok then return done("failed", results.map(_.copy(status = "failed", detail = "rejected by the kernel")),
        List("the kernel rejects the proof: " + replay.output.linesIterator.toList.takeRight(5).mkString("\n")))
    val ax = Lean.axioms(lake.elaborate(g.auditPath(n.id)).output)
    val used = g.auditedTheorems(n).flatMap(t => ax.getOrElse(t, List("<no audit result>"))).distinct.sorted
    val extra = used.filterNot(Lean.allowedAxioms)
    if extra.nonEmpty then done("failed", results, List(s"disallowed axioms: ${extra.mkString(", ")}"), used)
    else done("proven", results, Nil, used)

  /** The recorded check of a node, if still current. */
  def current(n: Node[?]): Option[NodeCheck] = checks.get(n.id).filter(_.hash == checkHash(n))

  /** The source files a node governs: a contract's implementation, a design decision's files. */
  def code(n: Node[?]): Option[Code] =
    // An implementation governs the files of its package: the directories of the code it refers to
    // and everything below them, except the model's file and files another node governs explicitly.
    val impl = kb.implementation(n).toList.flatMap { i =>
      val model = i.modelFile.map(f => Path.of(f).toAbsolutePath.normalize)
      i.sources.map(f => Path.of(f).toAbsolutePath.normalize.getParent).distinct.flatMap { dir =>
        if Files.isDirectory(dir) then Files.walk(dir).iterator.asScala.toList.filter(_.toString.endsWith(".scala")) else Nil
      }.map(_.toAbsolutePath.normalize).filterNot(p => model.contains(p) || governedExplicitly(p))
    }
    val files = n.governs.map(ws.root.resolve) ++ impl
    if files.isEmpty then None else Some(Code.of(ws.root, files))

  /** A node's link to its parent: `proven` (detail: `auto`, `authored`, `instantiation`), `open`,
    * `failed` or `unchecked`, with a detail. None for a root or a design decision.
    */
  def link(n: Node[?]): Json =
    def st(status: String, detail: String) = obj("status" -> str(status), "detail" -> str(detail))
    if n.parent.isEmpty || n.kind == NodeKind.Design then JNull
    else current(n) match
      case None => st("unchecked", if checks.contains(n.id) then "changed since the last check" else "not checked yet")
      case Some(c) => c.obligations.headOption match
        case Some(r) if r.status == "proven" && c.status == "failed" => st("failed", c.messages.headOption.getOrElse("the node's theorems do not build"))
        case Some(r) => st(r.status, r.detail)
        case None if c.status == "model-error" => st("failed", "the model does not build: " + c.messages.headOption.getOrElse(""))
        case None => st(if c.status == "failed" then "failed" else "proven", "instantiation")

  // ---------------------------------------------------------------------------
  // Decisions
  // ---------------------------------------------------------------------------

  /** Applies a developer's decision (see `Decisions.decide`) and records it in the ledger. */
  def decide(r: Decisions.Request): Either[String, Unit] =
    val files = kb.nodes.flatMap(code).flatMap(_.files).distinct
    Decisions.decide(baseSnapshot, ledger, r, java.time.Instant.now.toString, Git.snapshot(ws.root, files)).map(Ledger.save(ws.ledgerFile, _))

  /** Warnings about the record itself: decisions committed earlier and since rewritten, and
    * governed files that do not exist.
    */
  def integrity: List[String] =
    val rewritten = Ledger.rewrites(ws.root, ws.ledgerFile, ledger)
    val missing = kb.nodes.flatMap(n => n.governs.filterNot(f => Files.exists(ws.root.resolve(f))).map(f => s"${n.id} governs $f, which does not exist"))
    rewritten ++ missing ++ ungoverned.map(f => s"$f is governed by no node: govern it (.governing or a design node) or move it")

  /** Source files no node governs, other than the model's own: code that can change unnoticed. */
  def ungoverned: List[String] =
    val src = ws.root.resolve("src/main")
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val governed = kb.nodes.flatMap(code).flatMap(_.files).map(f => abs(ws.root.resolve(f))).toSet ++
      kb.implementations.flatMap(_.modelFile).map(f => abs(Path.of(f)))
    if !Files.isDirectory(src) then Nil
    else Files.walk(src).iterator.asScala.toList.filter(p => Files.isRegularFile(p) && p.toString.endsWith(".scala"))
      .map(abs).filterNot(governed).map(p => abs(ws.root).relativize(p).toString).sorted

  /** Where the developer stands on each node (see `Decisions`). */
  def state(n: Node[?]): String =
    annotated("nodes").get.arr.find(_("id").flatMap(_.str).contains(n.id)).flatMap(_("state")).flatMap(_.str).get

  def gone: List[String] = annotated("gone").get.arr.flatMap(_("id").flatMap(_.str)).toList

  /** Creates the proof file of a node with a stub for its obligation. */
  def scaffold(n: Node[?]): Boolean =
    val g = generate
    val path = ws.lean.resolve(g.proofsPath(n.id))
    if g.obligation(n).isEmpty || Files.exists(path) then false
    else
      write(path, g.proofFile(n))

  def tree(mark: Option[String] = None): String = Decisions.tree(annotated, mark)

  /** The tree and its warnings, and whether everything is settled (the CI gate). */
  def status: (String, Boolean) =
    val a = annotated
    val warnings = integrity
    val ok = Decisions.settled(a) && warnings.isEmpty
    (Decisions.tree(a) + "\n\n" + warnings.map("warning: " + _ + "\n").mkString +
      (if ok then "Every node is accepted, proven, and its examples pass."
       else "Not every node is accepted, proven, and passing its examples, or there are warnings.") + "\n", ok)

  /** Open requests from the developer (written by the browser). */
  def requests: List[Json] =
    read(ws.requestsFile).map(Json.parse(_).arr.toList).getOrElse(Nil).filter(_("status").flatMap(_.str).contains("open"))

  /** Everything known about a node: the idea, the vocabulary, the roots, the path from the root
    * with every decision, reason and rejected alternative, the node's state, and what the
    * developer asked for. This is what a fresh agent, or a new engineer, reads first.
    */
  def context(n: Node[?]): String =
    val g = generate
    val l = ledger
    val ann = annotated
    val st = ann("nodes").get.arr.map(x => x("id").flatMap(_.str).get -> x("state").flatMap(_.str).get).toMap
    val sb = StringBuilder()
    sb ++= s"# ${kb.name} / ${n.id}\n\n## Idea\n\n${idea.trim}\n\n"
    sb ++= "## Vocabulary (what the model's open terms mean in the world)\n\n"
    kb.opaques.foreach(o => sb ++= s"- type `${o.name}`: ${o.means}\n")
    kb.params.foreach(p => sb ++= s"- `${p.name}`: ${p.means}\n")
    sb ++= s"\n## Knowledge base\n\nRoots (one concern of the idea each): ${kb.roots.map(r => s"${r.id} — ${r.statement}").mkString("; ")}\n\n"
    sb ++= s"```\n${Decisions.tree(ann, Some(n.id))}\n```\n\n## Path from the root\n\n"
    kb.path(n).foreach { a =>
      sb ++= s"### ${a.id} (${a.kind.toString.toLowerCase}) [${st(a.id)}]\n\n${a.statement}\n\nWhy: ${a.why}\n\n"
      l.history(a.id).foreach { d =>
        d.action match
          case "accept"  => sb ++= s"Accepted by ${d.by}: ${d.reason}\n\n"
          case "confirm" => sb ++= s"Confirmed by ${d.by}: ${d.reason}\n\n"
          case "revisit" => sb ++= s"To revisit (${d.by}): ${d.reason}\n\n"
          case _         => ()
      }
      val alts = l.alternatives(a.id)
      def f(c: Json, k: String) = c(k).flatMap(_.str).getOrElse("")
      alts.foreach((id, c) => sb ++= s"- Rejected alternative $id: ${f(c, "statement")} (why: ${f(c, "why")})\n")
      if alts.nonEmpty then sb ++= "\n"
      def src(label: String, x: Lifted[?]) = sb ++= s"$label:\n```scala\n${x.source}\n```\n"
      a.spec.foreach(src("spec", _))
      a.abs.foreach(src("abs", _))
      a.post.foreach(src("post", _))
      a.substs.foreach(s => sb ++= s"- `${s.name} := ${s.term.fold(s.lean)(_.source)}`\n")
      kb.limits(a).foreach(x => sb ++= s"- does not promise: $x\n")
      kb.exampleResults(a).foreach { r =>
        sb ++= s"- example: ${r.example.describe} [contract ${r.contract}${r.implementation.fold("")(i => s", implementation $i")}]\n"
      }
      code(a).foreach(c => sb ++= s"- governs: ${c.files.mkString(", ")}\n")
      sb ++= "\n"
    }
    val children = kb.nodes.filter(_.parent.exists(_.id == n.id))
    if children.nonEmpty then
      sb ++= s"## Below ${n.id} (a change here may affect them)\n\n"
      children.foreach { c =>
        sb ++= s"- ${c.id} (${c.kind.toString.toLowerCase}) [${st(c.id)}]: ${c.statement} Why: ${c.why}\n"
        l.chosen(c.id).foreach(d => sb ++= s"  Accepted by ${d.by}: ${d.reason}\n")
      }
      sb ++= "\n"
    g.obligation(n).foreach { o =>
      val stl = current(n).flatMap(_.obligations.headOption).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail})" else ""}")
      sb ++= s"## Obligation of ${n.id} [$stl]\n\n${o.description}\n\n```lean\n${o.statement}\n```\n\n"
    }
    val asks = requests.filter(_("node").flatMap(_.str).contains(n.id))
    if asks.nonEmpty then
      sb ++= "## Open requests from the developer\n\n"
      asks.foreach(r => sb ++= s"- [${r("id").flatMap(_.str).getOrElse("")}] ${r("text").flatMap(_.str).getOrElse("")}\n")
      sb ++= "\n"
    sb ++= s"The developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).\n"
    sb.result()

  // ---------------------------------------------------------------------------
  // Snapshot: what the browser and agents read
  // ---------------------------------------------------------------------------

  /** The knowledge base as data, from the Scala definitions and the checks; without decisions. */
  def baseSnapshot: Json =
    val g = generate
    def strs(xs: Seq[String]) = JArr(xs.map(str))
    def node(n: Node[?]): Json =
      val check = current(n)
      obj(
        "id" -> str(n.id),
        "kind" -> str(n.kind.toString.toLowerCase),
        "parent" -> n.parent.fold(JNull)(p => str(p.id)),
        "limits" -> JArr(kb.limits(n).map(str)),
        "examples" -> JArr(kb.exampleResults(n).map(r => obj(
          "note" -> str(r.example.note), "given" -> strs(r.example.givens), "call" -> str(r.example.call),
          "expected" -> JBool(r.example.expected), "contract" -> str(r.contract),
          "implementation" -> r.implementation.fold(JNull)(str)))),
        "code" -> code(n).fold(JNull)(c => obj(
          "files" -> strs(c.files), "fingerprint" -> str(c.fingerprint))),
        "content" -> content(n),
        "hash" -> str(hash(n)),
        "chain" -> str(chainHash(n)),
        "link" -> link(n),
        "obligation" -> g.obligation(n).fold(JNull)(o => obj("statement" -> str(o.statement), "description" -> str(o.description))),
        "proof" -> read(ws.lean.resolve(g.proofsPath(n.id))).fold(JNull)(src => obj("file" -> str("lean/" + g.proofsPath(n.id)), "source" -> str(src))),
        "rootTheorem" -> str(if g.formal(n) then g.rootTheorem(n) else ""),
        "lean" -> str(if g.formal(n) then g.spec(n) else ""),
        "messages" -> strs(check.toList.flatMap(_.messages)),
        "axioms" -> strs(check.toList.flatMap(_.axioms))
      )
    obj(
      "name" -> str(kb.name),
      "idea" -> str(idea),
      "ideaFile" -> str(kb.idea),
      "warnings" -> JArr(integrity.map(str)),
      "roots" -> JArr(kb.roots.map(r => str(r.id))),
      "exportedAt" -> str(java.time.Instant.now.toString),
      "opaques" -> JArr(kb.opaques.map(o => obj("name" -> str(o.name), "means" -> str(o.means)))),
      "params" -> JArr(kb.params.map(p => obj(
        "name" -> str(p.name), "means" -> str(p.means),
        "type" -> str(kb.nodes.flatMap(_.lifted).flatMap(_.paramRefs).toMap.getOrElse(p.name, ""))))),
      "types" -> JArr(kb.types.map(t => obj("name" -> str(t.name), "lean" -> str(t.lean)))),
      "defs" -> JArr(kb.defs.map(d => obj("name" -> str(d.name), "source" -> str(d.lifted.source)))),
      "nodes" -> JArr(kb.ordered.map(node))
    )

  /** The snapshot with the developer's decisions. */
  def annotated: Json = Decisions.annotate(baseSnapshot, ledger)

  /** Writes the snapshot to `.frflow/kb.json`. The browser re-reads the ledger itself. */
  def writeSnapshot(): Path =
    Files.createDirectories(ws.snapshotFile.getParent)
    Files.writeString(ws.snapshotFile, baseSnapshot.render() + "\n", UTF_8)
    ws.snapshotFile
