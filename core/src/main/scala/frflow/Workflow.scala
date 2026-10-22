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

  /** The obligations proven by a theorem of their name in the node's proof file: (node, obligation). */
  def proofs: Set[(String, String)] =
    val base = Generate(kb)
    kb.nodes.flatMap { n =>
      val names = base.obligations(n).map(_.name).toSet + "feasible"
      read(ws.lean.resolve(base.proofsPath(n.id))).toList.flatMap(src => Lean.theorems(src).map(_.name).filter(names).map(n.id -> _))
    }.toSet

  /** Nodes whose link has an authored proof. */
  def authored(id: String): Boolean = proofs((id, "link"))

  def generate: Generate = Generate(kb, proofs)

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
    // Through every definition it uses, however nested, as for the Lean it depends on.
    val defs = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
    def visit(d: Def[?]): Unit = if !defs.contains(d.name) then { defs(d.name) = d; d.lifted.defs.foreach(visit) }
    n.referenced.flatMap(_.defs).foreach(visit)
    val used = n.referenced ++ defs.values.map(_.lifted)
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
    "uses" -> JArr(generate.sourcesUsedBy(n).map(str)),
    "governs" -> JArr(n.governs.map(str))
  ) ++ (if n.formal then Nil else List("formal" -> JBool(false))) ++
    (if n.kept.isEmpty then Nil else List("keeps" -> JArr(n.kept.map(k => str(k.describe))))) ++
    kb.implementation(n).flatMap(_.proven).map { d =>
      val all = scala.collection.mutable.LinkedHashMap.empty[String, Def[?]]
      def visit(x: Def[?]): Unit = if !all.contains(x.name) then { all(x.name) = x; x.lifted.defs.foreach(visit) }
      visit(d)
      "implementation" -> str(("proven: " + d.name) +: all.values.map(x => s"${x.name} = ${x.lifted.source}").toList mkString "\n")
    }.toList ++ kb.implementation(n).filter(_.proven.isEmpty).filter(_.wiring.nonEmpty).map(i => "implementation" -> str(i.wiring)).toList
    ++ (if n.kind != NodeKind.Root then Nil
        else if n.ideaSection.isEmpty then Seq("idea" -> str(ideaDecided), "notModelled" -> str(notModelled))
        else Seq("idea" -> str(ideaOf(n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(notModelled))))

  /** The part of the idea a root is decided against: its section, after the text before the first. */
  def ideaOf(root: Node[?]): String =
    val (intro, sections) = Decisions.ideaSections(ideaDecided)
    (intro :: sections.find(_._1.equalsIgnoreCase(root.ideaSection.trim)).map(_._2).toList).filter(_.nonEmpty).mkString("\n\n")

  /** Sections of the idea no root is decided against, when roots name sections; roots naming a missing one. */
  def ideaCoverage: List[String] =
    val named = kb.roots.map(_.ideaSection.trim).filter(_.nonEmpty)
    val sections = Decisions.ideaSections(ideaDecided)._2.map(_._1)
    if named.isEmpty then Nil
    else sections.filterNot(h => named.exists(_.equalsIgnoreCase(h)))
        .map(h => s"the section \"$h\" of ${kb.idea} is the concern of no root: add a root for it (idea = \"$h\"), or move it to Not modelled") ++
      kb.roots.filter(_.ideaSection.trim.nonEmpty).filterNot(r => sections.exists(_.equalsIgnoreCase(r.ideaSection.trim)))
        .map(r => s"${r.id} is decided against the section \"${r.ideaSection}\", which ${kb.idea} does not have") ++
      kb.roots.filter(_.ideaSection.trim.isEmpty).map(r => s"${r.id} names no section of ${kb.idea}, though other roots do: name the one it is decided against")

  def hash(n: Node[?]): String = Decision.hash(content(n))

  /** The node's content together with its ancestors': a change anywhere above shows below.
    * What is not modelled is reviewed at the roots only: it narrows no node below them.
    */
  def chainHash(n: Node[?]): String =
    Decisions.chain(content(n), Decisions.above(if n.kind == NodeKind.Design then "" else n.parent.fold("")(chainHash),
      n.kept.filter(_.view.nonEmpty).map(k => chainHash(k.invariant))))

  /** Files governed explicitly by some node. */
  private lazy val governedExplicitly: Set[Path] =
    kb.nodes.flatMap(_.governs).map(f => ws.root.resolve(f).toAbsolutePath.normalize).toSet

  /** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. */
  def checkHash(n: Node[?]): String =
    val g = generate
    sha((Seq(g.spec(n), g.auto(n), g.theorems(n), g.extraObligations(n).map(g.oblFile(n, _)).mkString, g.rootImplFile(n).getOrElse(""), g.saysNothing(n).map(_.obligation.statement).mkString, read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse(""),
      read(ws.lean.resolve(g.proofsPath(n.id))).filter(Lean.lemmaImports(_).nonEmpty).flatMap(_ => read(ws.lean.resolve(g.lemmasPath))).getOrElse(""),
      n.parent.fold("")(checkHash), kernelHash, Workflow.CheckerVersion.toString) ++ g.declarationsUsedBy(n))*)

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

    // Lemmas shared by the proof files: the same filter, built, and replayed through the kernel.
    val proofSrc = read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse("")
    val lemmas = Lean.lemmaImports(proofSrc)
    if lemmas.nonEmpty then
      if lemmas != List(g.lemmasModule) then return done("failed", Nil, List(s"a proof file may import only ${g.lemmasModule}, not ${lemmas.mkString(", ")}"))
      val lsrc = read(ws.lean.resolve(g.lemmasPath))
      if lsrc.isEmpty then return done("failed", Nil, List(s"the proof imports ${g.lemmasModule}, but lean/${g.lemmasPath} does not exist"))
      val bad = Lean.violations(lsrc.get) ++ Lean.lemmaImports(lsrc.get).map(m => (0, s"import $m"))
      if bad.nonEmpty then return done("failed", Nil, List(s"not allowed in lean/${g.lemmasPath}: ${bad.map(_._2).distinct.mkString(", ")}"))
      val built = lake.build(g.lemmasModule)
      if !built.ok then return done("failed", Nil, "the lemmas do not build" :: errors(built))
      if Lean.usesSorry(built.output) then return done("failed", Nil, List(s"lean/${g.lemmasPath} uses sorry"))
      val replay = lake.replay(g.lemmasModule)
      if !replay.ok then return done("failed", Nil, List("the kernel rejects the lemmas: " + replay.output.linesIterator.toList.takeRight(5).mkString("\n")))

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
    // What would make the node say nothing: a claim holding without its premise, no model, the root by itself.
    val empty = g.saysNothing(n).filter(e => lake.elaborate(g.oblPath(n.id, e.obligation.name)).ok)
    val emptyLink = empty.find(_.fails == "link")
    if emptyLink.isDefined then
      return done("failed", results.map(_.copy(status = "failed", detail = emptyLink.get.why)), List(emptyLink.get.message))
    if parentStatus.exists(_ != "proven") then return done("waiting", results, List(s"waiting for ${n.parent.get.id}"))

    val thms = lake.build(g.theoremsModule(n.id))
    if !thms.ok then return done("failed", results, "the node's theorems do not build" :: errors(thms))
    // Replay the authored proof through the kernel, so nothing elaborated around it is trusted.
    if authored(n.id) then
      val replay = lake.replay(g.proofsModule(n.id))
      if !replay.ok then return done("failed", results.map(_.copy(status = "failed", detail = "rejected by the kernel")),
        List("the kernel rejects the proof: " + replay.output.linesIterator.toList.takeRight(5).mkString("\n")))
    val ax = Lean.axioms(lake.elaborate(g.auditPath(n.id)).output)
    // The other obligations (kept invariants, a proven implementation), each in a file of its own:
    // proven by frflow_auto or by a theorem in the proof file, which is built and replayed here when
    // the link does not build it.
    if g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) && !authored(n.id) then
      val src = read(ws.lean.resolve(g.proofsPath(n.id))).getOrElse("")
      val bad = Lean.violations(src)
      if bad.nonEmpty then return done("failed", results, List(s"not allowed in a proof file: ${bad.map(_._2).distinct.mkString(", ")}"))
      val built = lake.build(g.proofsModule(n.id))
      if !built.ok then return done("failed", results, "the proof file does not build" :: errors(built))

      val replay = lake.replay(g.proofsModule(n.id))
      if !replay.ok then return done("failed", results, List("the kernel rejects the proof file: " + replay.output.linesIterator.toList.takeRight(5).mkString("\n")))
    val invRuns = g.extraObligations(n).map { o =>
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      empty.find(_.fails == o.name) match
        case Some(e) => (Result(o.name, "failed", e.why), Nil)
        case None =>
          val run = lake.elaborate(g.oblPath(n.id, o.name))
          // Fail closed: the theorem's own audit must be there.
          val audit = Lean.axioms(run.output).collectFirst { case (t, as) if t == o.name || t.endsWith("." + o.name) => as }
          val r = if run.ok && (Lean.usesSorry(run.output) || audit.exists(_.contains("sorryAx"))) then Result(o.name, "open", "uses sorry")
            else if run.ok then Result(o.name, "proven", how)
            else Result(o.name, "open", s"not proven ($how): prove theorem ${o.name} : Obl.${o.name} in lean/${g.proofsPath(n.id)}")
          (r, if r.status == "proven" then audit.getOrElse(List("<no audit result>")) else Nil)
    }
    // With a proven implementation, the root theorem of the code itself.
    val rootImpl = g.rootImplFile(n).filter(_ => invRuns.exists((r, _) => r.name == "impl" && r.status == "proven")).map { _ =>
      val built = lake.build(g.oblModule(n.id, "impl"))
      val run = if built.ok then lake.elaborate(g.oblPath(n.id, "rootImpl")) else built
      val audit = Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith(".root_impl") || t == "root_impl" => as }
      if run.ok then (Result("root_impl", "proven", "the root holds of the implementation"), audit.getOrElse(List("<no audit result>")))
      else (Result("root_impl", "failed", "the root theorem of the implementation does not build: " + errors(run).mkString("; ").take(300)), Nil)
    }.toList
    val invRunsAll = invRuns ++ rootImpl
    val used = (g.auditedTheorems(n).flatMap(t => ax.getOrElse(t, List("<no audit result>"))) ++ invRunsAll.flatMap(_._2)).distinct.sorted
    val extra = used.filterNot(Lean.allowedAxioms)
    val all = results ++ invRunsAll.map(_._1)
    if extra.nonEmpty then done("failed", all, List(s"disallowed axioms: ${extra.mkString(", ")}"), used)
    else done("proven", all, invRunsAll.collect { case (r, _) if r.status != "proven" => r.detail }, used)

  /** The recorded check of a node, if still current. */
  def current(n: Node[?]): Option[NodeCheck] =
    // A committed record of checks is not evidence: proofs come from running check.
    if !generate.formal(n) || checksCommitted then None else checks.get(n.id).filter(_.hash == checkHash(n))

  /** Whether `.frflow/checks.json` is in git: it must not be, since anyone can edit it. */
  lazy val checksCommitted: Boolean = Git.tracked(ws.root, ws.root.relativize(ws.checksFile).toString)

  /** The source files a node governs: a contract's implementation, a design decision's files. */
  def code(n: Node[?]): Option[Code] =
    // An implementation governs the files of the code its expression refers to (not the model's
    // file); anything else it depends on is governed explicitly (.governing, or a design node owning a
    // directory), or `status` reports it as governed by no node.
    val impl = kb.implementation(n).toList.flatMap { i =>
      i.sources.map(f => Path.of(f).toAbsolutePath.normalize).filterNot(p => governedExplicitly.exists(g => p == g || p.startsWith(g)))
    }
    val files = n.governs.map(ws.root.resolve) ++ impl
    if files.isEmpty then None else Some(Code.of(ws.root, files))

  /** A node's link to its parent: `proven` (detail: `auto`, `authored`, `instantiation`), `open`,
    * `failed` or `unchecked`, with a detail. None for a root or a design decision.
    */
  def link(n: Node[?]): Json =
    def st(status: String, detail: String) = obj("status" -> str(status), "detail" -> str(detail))
    if n.parent.isEmpty || n.kind == NodeKind.Design then JNull
    else if !n.formal then st("informal", "not formalized: decided by reading")
    else current(n) match
      case None => st("unchecked", if checks.contains(n.id) then "changed since the last check" else "not checked yet")
      case Some(c) => c.obligations.headOption match
        case Some(r) if r.status == "proven" && c.status == "failed" => st("failed", c.messages.headOption.getOrElse("the node's theorems do not build"))
        // An authored link counts once something is shown to meet the node.
        case Some(r) if r.status == "proven" && c.obligations.exists(o => o.name == "feasible" && o.status != "proven") =>
          st("open", "the link is proven by hand: prove `feasible` too (some model meets the node), or give a proven implementation")
        case Some(r) => st(r.status, r.detail)
        case None if c.status == "model-error" => st("failed", "the model does not build: " + c.messages.headOption.getOrElse(""))
        case None => st(if c.status == "failed" then "failed" else "proven", "instantiation")

  // ---------------------------------------------------------------------------
  // Decisions
  // ---------------------------------------------------------------------------

  /** Applies a decision (see `Decisions.decide`) to a fresh snapshot and records it: for programs and
    * tests. The browser decides through `tools.Project`, on the snapshot the developer saw.
    */
  def decide(r: Decisions.Request): Either[String, Unit] =
    val files = kb.nodes.flatMap(code).flatMap(_.files).distinct
    Decisions.decide(baseSnapshot, ledger, r, java.time.Instant.now.toString, Git.head(ws.root), Git.snapshot(ws.root, files))
      .map(Ledger.save(ws.ledgerFile, _))

  /** Warnings about the record itself: decisions committed earlier and since rewritten, and
    * governed files that do not exist.
    */
  def integrity: List[String] = Ledger.warnings(ws.root, ws.ledgerFile, ledger) ++ codeWarnings

  /** Warnings about the model and the code (the ledger's are read live, see `Ledger.warnings`). */
  def codeWarnings: List[String] =
    val missing = kb.nodes.flatMap(n => n.governs.filterNot(f => Files.exists(ws.root.resolve(f))).map(f => s"${n.id} governs $f, which does not exist"))
    // One owner per file: two nodes governing it would each review it as its own.
    val owners = kb.nodes.flatMap(n => code(n).toList.flatMap(_.files).map(_ -> n.id)).groupBy(_._1).toList.sortBy(_._1)
      .collect { case (f, ns) if ns.map(_._2).distinct.size > 1 => s"$f is governed by ${ns.map(_._2).distinct.mkString(" and ")}: give it one owner" }
    missing ++ owners ++ ideaCoverage ++
      staleNames ++
      (if checksCommitted then List(".frflow/checks.json is committed: proof results must come from running check, so it is ignored; remove it from git") else Nil) ++ ungoverned.map(f => s"$f is governed by no node: govern it (.governing or a design node) or move it") ++
      modelCode

  /** Statements and reasons that name a node no longer chosen (rejected, or removed): the text
    * still rests on it.
    */
  def staleNames: List[String] =
    val l = ledger
    val ids = kb.nodes.map(_.id).toSet
    val dropped = l.decisions.keySet.filter(id => id != Ledger.Self &&
      (l.current(id).exists(_.action == "remove") || l.current(id).exists(_.action == "reject"))).toSet
    kb.nodes.filterNot(n => l.current(n.id).exists(_.action == "reject")).flatMap { n =>
      dropped.toList.sorted.filter(d => d != n.id && s"\\b${java.util.regex.Pattern.quote(d)}\\b".r.findFirstIn(n.statement + " " + n.why).isDefined)
        .map(d => s"${n.id}: its statement or why names $d, which is ${if ids(d) then "rejected" else "removed"}")
    }

  /** Code in the model's file that is not the model: no node governs it, so it could change
    * unnoticed. The model's file holds the model's vals (nodes, opaque types, parameters, definitions), domain
    * types without methods, and the `@main` of the CLI; anything else belongs next to the code.
    */
  def modelCode: List[String] =
    val skip = Set("final", "private", "protected", "sealed", "abstract", "lazy", "override", "inline", "opaque", "transparent")
    kb.modelFiles.map(f => Path.of(f)).filter(Files.isRegularFile(_)).flatMap { p =>
      val rel = ws.root.toAbsolutePath.normalize.relativize(p.toAbsolutePath.normalize)
      var inEnum = false
      // Strings (statements, reasons) say anything; only the code around them is looked at.
      Files.readAllLines(p).asScala.toList.map(_.replaceAll("\"(\\\\.|[^\"\\\\])*\"", "\"\"")).zipWithIndex.flatMap { (l, i) =>
        val t = l.trim
        val top = l.nonEmpty && !l.head.isWhitespace
        val words = t.split("\\s+").toList.dropWhile(skip)
        val word = words.headOption.getOrElse("")
        val withBody = t.endsWith(":") || t.contains("{")
        if top then inEnum = word == "enum"
        // A top-level val must be part of the model: an opaque type, a parameter, a definition, a node
        // or the knowledge base.
        val modelVal = """val\s+\w+\s*(:[^=]*)?=\s*(Opaque\(|Param\[|define\s*\{|Node\.(root|design|invariant)\b|KnowledgeBase\(|\w+\s*\.\s*(refine|instantiate|contract|design)\s*[\[(]).*""".r
        // ...and a definition, parameter or opaque type no node uses is code no node governs.
        val termVal = """val\s+(\w+)\s*(:[^=]*)?=\s*(Opaque|Param|define)\b.*""".r
        val used = (kb.defs.map(_.name) ++ kb.params.map(_.name) ++ kb.opaques.map(_.name)).map(_.stripPrefix("«").stripSuffix("»")).toSet
        val bad =
          if top then
            !t.startsWith("@main") && !t.startsWith("//") && !t.startsWith("/*") && !t.startsWith("*") && (
              Set("def", "class", "object", "given", "extension", "implicit", "type", "var")(word) ||
              (word == "trait" && withBody) || (word == "case" && withBody) ||
              (word == "val" && !modelVal.matches(words.mkString(" "))) ||
              (word == "val" && (words.mkString(" ") match
                case termVal(name, _, _) => !used(name)
                case _                   => false)))
          else word == "def" || (inEnum && word != "case" && word.nonEmpty && !word.startsWith("//")) ||
            // code hidden after a separator, as in `; object X { ... }`
            """(^|;|\{)\s*(def|object|class|trait|given|var)\s""".r.findFirstIn(l).exists(_ => !t.startsWith("//"))
        if bad then List(s"$rel:${i + 1}: `${t.take(50)}` is code in the model's file, which no node governs; move it next to the implementation")
        else Nil
      }
    }

  /** Source files no node governs, other than the model's own: code that can change unnoticed. */
  def ungoverned: List[String] =
    val src = ws.root.resolve("src/main")
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val governed = kb.nodes.flatMap(code).flatMap(_.files).map(f => abs(ws.root.resolve(f))).toSet ++
      kb.modelFiles.map(f => abs(Path.of(f)))
    if !Files.isDirectory(src) then Nil
    else Files.walk(src, java.nio.file.FileVisitOption.FOLLOW_LINKS).iterator.asScala.toList.filter(Files.isRegularFile(_))
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
    val ok = Decisions.complete(a) && warnings.isEmpty
    val notes = Ledger.restarts(ws.root, ws.ledgerFile).filter(c => ledger.acknowledged.exists(c.startsWith))
      .map(c => s"the ledger was restarted in commit ${c.take(10)} (acknowledged); earlier decisions are in git history")
    val pending = Decisions.unendorsed(a)
    (Decisions.tree(a) + "\n\n" + notes.map("note: " + _ + "\n").mkString + warnings.map("warning: " + _ + "\n").mkString +
      (if pending.nonEmpty then s"The agent settled ${pending.mkString(", ")}: the developer endorses it in the browser before this passes.\n" else "") +
      (if ok then "Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass."
       else "Not every node is accepted, proven, and passing its examples, or there are warnings.") + "\n", ok)

  /** Open requests from the developer (written by the browser). */
  def requests: List[Json] = allRequests.filter(_("status").flatMap(_.str).contains("open"))
  def allRequests: List[Json] = read(ws.requestsFile).map(Json.parse(_).arr.toList).getOrElse(Nil)

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
          case "accept" if l.chosen(a.id).contains(d) => sb ++= s"Chosen by ${d.by} because: ${d.reason}\n\n"
          case "accept"  => sb ++= s"Change accepted by ${d.by}: ${d.reason}\n\n"
          case "confirm" => sb ++= s"Confirmed by ${d.by}: ${d.reason}\n\n"
          case "revisit" => sb ++= s"To revisit (${d.by}): ${d.reason}\n\n"
          case "settle"  => sb ++= s"Settled by the agent: ${d.reason}\n\n"
          case _         => ()
      }
      l.considered(a.id).take(3).foreach((by, d) => sb ++= s"Considered when $by changed (${d.by}): still holds\n\n")
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
    // The cross-cutting rules that reach this node: every contract in their scope keeps them or is exempt.
    val invs = kb.nodes.filter(i => i.kind == NodeKind.Invariant &&
      (i eq n) || (i.kind == NodeKind.Invariant && (i.scope.isEmpty || kb.path(n).exists(a => i.scope.exists(_ eq a)))))
    if invs.nonEmpty then
      sb ++= "## Invariants that apply here (every contract in their scope keeps them, or says why not)\n\n"
      invs.foreach { i =>
        sb ++= s"### ${i.id} [${st(i.id)}]\n\n${i.statement}\n\nWhy: ${i.why}\n\n"
        l.chosen(i.id).foreach(d => sb ++= s"Chosen by ${d.by} because: ${d.reason}\n\n")
        i.spec.foreach(r => sb ++= s"rule:\n```scala\n${r.source}\n```\n")
        i.scope.headOption.foreach(_ => sb ++= s"- scope: below ${i.scope.map(_.id).mkString(", ")}\n")
        kb.nodes.flatMap(c => c.kept.filter(_.invariant eq i).map(c -> _)).foreach { (c, k) =>
          sb ++= k.view.fold(s"- ${c.id} is exempt: ${k.exempt}\n")(v => s"- kept by ${c.id}, showing the rule: `${v.source}`\n")
        }
        sb ++= "\n"
      }
    val me = ann("nodes").get.arr.find(_("id").flatMap(_.str).contains(n.id)).get
    val causes = me("causes").map(_.arr.flatMap(_.str).toList).getOrElse(Nil)
    if causes.nonEmpty then
      sb ++= s"## What moved since ${n.id} was decided: ${causes.mkString(", ")}\n\n"
      def fields(before: Json, now: Json): String =
        def flat(c: Json): Map[String, String] = c.obj.map((k, v) => k -> (v match
          case JStr(x) => x
          case JArr(xs) => xs.map(x => x.str.getOrElse(x.compact)).mkString("\n")
          case other    => other.compact)).toMap
        val (b, a) = (flat(before), flat(now))
        (b.keySet ++ a.keySet).toList.sorted.filter(k => b.get(k) != a.get(k)).map { k =>
          s"  - $k\n    was: ${b.getOrElse(k, "").replace("\n", "\n         ")}\n    now: ${a.getOrElse(k, "").replace("\n", "\n         ")}\n"
        }.mkString
      if causes.contains("self") then
        l.binding(n.id).foreach(d => sb ++= s"- ${n.id} itself changed:\n${fields(d.content, me("content").getOrElse(JNull))}")
      me("moved").map(_.arr.toList).getOrElse(Nil).foreach { m =>
        val a = m("id").flatMap(_.str).getOrElse("")
        val now = ann("nodes").get.arr.find(_("id").flatMap(_.str).contains(a)).flatMap(_("content")).getOrElse(JNull)
        sb ++= s"- the meaning of $a changed:\n${fields(m("before").getOrElse(JNull), now)}"
      }
      n.parent.filter(p => st(p.id) == "rejected").foreach(p => sb ++= s"- its parent ${p.id} was rejected: move it under the node chosen instead\n")
      if causes.contains("revisit") then
        l.current(n.id).filter(_.action == "revisit").foreach { r =>
          sb ++= s"- ${r.by} asked to revisit it: ${r.reason}\n"
          // The change that asked for it: decided at the same moment, with what it changed.
          l.all.collect { case (x, d) if x != n.id && d.at == r.at && d.action == "accept" => x -> d }.foreach { (x, d) =>
            val before = l.history(x).takeWhile(_ ne d).reverse.find(e => Ledger.binds(e.action))
            before.foreach(b => sb ++= s"  ${x} changed then:\n${fields(b.content, d.content).linesIterator.map("  " + _).mkString("\n")}\n")
          }
        }
      if causes.contains("code") then
        val since = l.developerBinding(n.id).orElse(l.binding(n.id)).map(d => if Git.has(ws.root, d.tree) then d.tree else d.commit).getOrElse("")
        val d = code(n).fold("")(c => Git.diff(ws.root, since, c.files))
        sb ++= (if d.nonEmpty then s"- the code it governs changed:\n```diff\n$d```\n" else "- the code it governs changed (no git diff available)\n")
      sb ++= "\n"
    def below(x: Node[?], depth: Int): List[(Node[?], Int)] =
      kb.nodes.filter(_.parent.exists(_.id == x.id)).flatMap(c => (c, depth) :: below(c, depth + 1))
    val under = below(n, 0)
    if under.nonEmpty then
      sb ++= s"## Below ${n.id}, with their reasons (a change here may affect them)\n\n"
      under.foreach { (c, depth) =>
        val pad = "  " * depth
        sb ++= s"$pad- ${c.id} (${c.kind.toString.toLowerCase}) [${st(c.id)}]: ${c.statement} Why: ${c.why}\n"
        l.chosen(c.id).foreach(d => sb ++= s"$pad  Chosen by ${d.by} because: ${d.reason}\n")
        l.considered(c.id).take(3).foreach((by, d) => sb ++= s"$pad  Considered when $by changed (${d.by}): still holds\n")
      }
      sb ++= "\n"
    g.obligation(n).foreach { o =>
      val stl = current(n).flatMap(_.obligations.headOption).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail})" else ""}")
      sb ++= s"## Obligation of ${n.id} [$stl]\n\n${o.description}\n\n```lean\n${o.statement}\n```\n\n"
    }
    val asks = allRequests.filter(_("node").flatMap(_.str).contains(n.id))
    if asks.nonEmpty then
      sb ++= "## Requests from the developer\n\n"
      asks.foreach { r =>
        def f(k: String) = r(k).flatMap(_.str).getOrElse("")
        sb ++= s"- [${f("id")}, ${f("status")}] ${f("text")}${if f("answer").nonEmpty then s"\n  Answer: ${f("answer")}" else ""}\n"
      }
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
        "invariants" -> JArr(n.kept.map { k =>
          val name = s"inv_${k.invariant.id}"
          val (st, detail) =
            if k.view.isEmpty then ("exempt", k.exempt)
            else if !g.formalKeeps(n).exists(_._1 eq k.invariant) then ("informal", "checked on the examples and at run time; not formalized")
            else check.flatMap(_.obligations.find(_.name == name)).fold(("unchecked", "not checked yet"))(r => (r.status, r.detail))
          obj("id" -> str(k.invariant.id), "view" -> str(k.view.fold("")(_.source)),
            "rule" -> str(k.invariant.spec.fold("")(_.source)), "status" -> str(st), "detail" -> str(detail))
        }),
        "implementationProof" -> kb.implementation(n).flatMap(_.proven).fold(JNull) { d =>
          val (st, detail) =
            if !g.formal(n) then ("informal", "the contract is out of Lean: checked on the examples and at run time")
            else check.flatMap(c => c.obligations.find(_.name == "impl").map(r =>
              c.obligations.find(_.name == "root_impl").filter(_ => r.status == "proven").fold((r.status, r.detail))(ri => (ri.status, ri.detail))))
              .getOrElse(("unchecked", "not checked yet"))
          obj("name" -> str(d.name), "status" -> str(st), "detail" -> str(detail))
        },
        "covers" -> JArr(if n.kind != NodeKind.Invariant then Nil else kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty)).map(c => str(c.id))),
        "exempts" -> JArr(if n.kind != NodeKind.Invariant then Nil else kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty)).map(c => str(c.id))),
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
      "format" -> JNum(Workflow.ContentFormat),
      "ideaFile" -> str(kb.idea),
      "warnings" -> JArr(codeWarnings.map(str)),
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

object Workflow:
  /** The shape of a node's content, which decisions are bound to. A snapshot of another shape is
    * not decided on: it was written by another version of FrFlow, and must be rendered again.
    */
  val ContentFormat: Int = 2

  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 2
