package frflow

import java.nio.charset.StandardCharsets.UTF_8
import frflow.Json.*
import java.nio.file.{Files, Path, StandardOpenOption}
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
  private def sha(parts: String*): String = Sha.parts(parts*)

  def idea: String = read(ws.root.resolve(kb.idea)).getOrElse("")
  def ledger: Ledger = Workflow.withImports(Ledger.load(ws.ledgerFile), importDirs)
  /** Each imported node, and the directory of the project that decides it. */
  def importDirs: Map[String, String] = kb.imports.view.mapValues(i => ws.root.resolve(i.root).toAbsolutePath.normalize.toString).toMap
  private var checksCache: Option[(String, Map[String, NodeCheck])] = None
  /** The recorded checks (read again when the file changes). */
  def checks: Map[String, NodeCheck] = synchronized {
    val f = ws.checksFile
    val stamp = if Files.exists(f) then s"${Files.size(f)}:${Files.getLastModifiedTime(f).toMillis}" else ""
    checksCache.filter(_._1 == stamp).map(_._2).getOrElse { val c = Checks.load(f); checksCache = Some(stamp -> c); c }
  }

  /** The obligations proven by a theorem of their name in the node's proof file: (node, obligation). */
  def proofs: Set[(String, String)] =
    val base = baseGenerate
    kb.nodes.flatMap { n =>
      val names = base.obligations(n).map(_.name).toSet + "feasible"
      read(ws.lean.resolve(base.proofsPath(n.id))).toList.flatMap(src => Lean.theorems(src).map(_.name).filter(names).map(n.id -> _))
    }.toSet

  /** Nodes whose `complete` has an authored proof. */
  def authored(id: String): Boolean = proofs((id, "complete"))

  /** The definitions the developer chose (accepted, and not since rejected): among two definitions of a
    * term, the one in force.
    */
  def chosen(id: String): Boolean = ledger.binding(id).isDefined && !ledger.current(id).exists(_.action == "reject")

  private lazy val baseGenerate = Generate(kb)

  /** The proof files as they are now (names, sizes, times), and the definitions chosen among
    * alternatives: what `generate` and check hashes are cached by.
    */
  private def proofStamp: String =
    val dir = ws.lean.resolve(baseGenerate.proofsPath("x")).getParent
    val files = if !Files.isDirectory(dir) then ""
      else scala.util.Using.resource(Files.list(dir))(_.iterator.asScala.toList).sorted
        .map(f => s"${f.getFileName}:${Files.size(f)}:${Files.getLastModifiedTime(f).toMillis}").mkString(",")
    files + "|" + kb.definitionsOf.values.filter(_.size > 1).flatten.map(_.id).filter(chosen).toList.sorted.mkString(",")
  private var cached: Option[(String, Generate, scala.collection.concurrent.TrieMap[String, String])] = None
  private def cache: (Generate, scala.collection.concurrent.TrieMap[String, String]) = synchronized {
    importProofs()
    val stamp = proofStamp
    cached.filter(_._1 == stamp).fold { val c = (stamp, Generate(kb, proofs, chosen), scala.collection.concurrent.TrieMap.empty[String, String]); cached = Some(c); (c._2, c._3) }(c => (c._2, c._3))
  }
  def generate: Generate = cache._1

  /** The proofs another knowledge base wrote for the nodes this one imports, copied beside this one's
    * (its names in place of the other's): imported nodes are proven here too, as they stand here.
    */
  private def importProofs(): Unit =
    kb.imports.foreach { (id, i) =>
      val dir = ws.root.resolve(i.root).normalize
      val src = Option(dir.resolve(s"lean/Proofs/${i.kb}/$id.lean")).filter(Files.isRegularFile(_)).map(Files.readString(_, UTF_8))
      val dst = ws.lean.resolve(baseGenerate.proofsPath(id))
      src.fold(if Files.isRegularFile(dst) && read(dst).exists(_.startsWith(Workflow.CopiedProof)) then Files.delete(dst)) { text =>
        write(dst, s"${Workflow.CopiedProof} ${i.kb}: edit it there.\n" +
          text.replaceAll(s"\\b${java.util.regex.Pattern.quote(i.kb)}\\.", java.util.regex.Matcher.quoteReplacement(kb.name + ".")))
      }
    }

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

  /** The idea a root is decided against: IDEA.md without its `## Not modelled` section. */
  def ideaDecided: String = Decisions.splitIdea(idea)._1

  /** The `## Not modelled` section of IDEA.md: the limits of the theory. */
  def notModelled: String = Decisions.splitIdea(idea)._2

  /** What is not modelled, as a root is decided against it: the text before the first `### `
    * subsection (every root's), and the subsection named as the root's idea section. An edit of one
    * root's subsection reviews only that root.
    */
  def notModelledOf(root: Node[?]): String = notModelledOfText(notModelled, root)

  private def notModelledOfText(notModelled: String, root: Node[?]): String =
    val lines = notModelled.linesIterator.toList
    val (general, rest) = lines.span(l => !l.startsWith("### "))
    def go(ls: List[String]): List[(String, String)] = ls match
      case h :: tail =>
        val (body, more) = tail.span(l => !l.startsWith("### "))
        (h.stripPrefix("### ").trim -> (h :: body).mkString("\n").trim) :: go(more)
      case Nil => Nil
    val own = go(rest).filter((h, _) => root.ideaSection.trim.nonEmpty && h.equalsIgnoreCase(root.ideaSection.trim)).map(_._2)
    (general.mkString("\n").trim :: own).filter(_.nonEmpty).mkString("\n\n")

  /** The terms a node mentions, with what they mean in the world. */
  def vocabulary(n: Node[?]): List[String] =
    val terms = kb.termsOf(n).toSet ++ n.defines
    (kb.opaques.filter(o => terms(o.name)).map(o => s"${o.name}: ${o.means}") ++ kb.params.filter(p => terms(p.name)).map(p => s"${p.name}: ${p.means}")).sorted

  /** The node as the developer sees it and decides it. A decision is bound to its hash. */
  def content(n: Node[?]): Json = JObj(Seq(
    "kind" -> str(Workflow.kindName(n)),
    "parents" -> JArr(n.parents.map(p => str(p.id))),
    "statement" -> str(n.statement),
    "why" -> str(n.why),
    "sources" -> JObj(Seq("formula" -> n.formula, "post" -> n.post, "rule" -> n.rule, "check" -> n.local).collect { case (k, Some(l)) => k -> str(l.source) }),
    "substitutions" -> JArr(n.substs.map(s => str(s"${s.name} := ${s.term.fold(s.lean)(_.source)}"))),
    "examples" -> JArr(n.cases.map(e => str(e.describe))),
    "vocabulary" -> JArr(vocabulary(n).map(str)),
    "uses" -> JArr(generate.sourcesUsedBy(n).map(str)),
    "governs" -> JArr(n.governs.map(str)),
    "definition" -> str(definition(n))
  ) ++ n.op.map(o => "op" -> str(o.name)) ++ n.replaced.map(r => "replaces" -> str(r.id)) ++
    (if n.formal then Nil else List("formal" -> JBool(false))) ++
    (if n.kept.isEmpty then Nil else List("keeps" -> JArr(n.kept.map(k => str(k.describe))))) ++
    (if n.expected.isEmpty then Nil else List("expects" -> JArr(n.expected.map((st, l) => str(s"$st: ${l.source}"))))) ++
    kb.implementation(n).flatMap { i =>
      val proven = i.proven.toList.flatMap(d => s"proven: ${d.name}" +: Def.closure(List(d)).map(x => s"${x.name} = ${x.lifted.source}"))
      val runs = Option.when(i.wiring.nonEmpty)(if i.proven.isDefined then s"runs: ${i.wiring}" else i.wiring).toList
      Option.when((proven ++ runs).nonEmpty)("implementation" -> str((proven ++ runs).mkString("\n")))
    }.toList
    ++ {
      // The root is decided against the idea's title and lead; a node naming a section, against that section.
      // Another knowledge base's node is decided against its own idea.
      val (decided, notM) = kb.imports.get(n.id).fold((ideaDecided, notModelled))(i =>
        Decisions.splitIdea(read(Path.of(i.root).resolve(i.idea)).getOrElse("")))
      if n.ideaSection.nonEmpty then Seq("idea" -> str(ideaOfText(decided, n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(notModelledOfText(notM, n)))
      else if kb.root.exists(_ eq n) then Seq("idea" -> str(Decisions.ideaSections(decided)._1), "notModelled" -> str(notModelledOfText(notM, n)))
      else Nil
    })

  /** The source of the top-level definition a node is written in (the `val` with every call chained on
    * it, its arguments, its examples): what the developer decides is what is written, so nothing hidden in
    * an argument (a block that runs code before giving a `why`) escapes review.
    */
  def definition(n: Node[?]): String =
    read(Path.of(n.file)).orElse(read(ws.root.resolve(n.file))).filter(_ => n.at >= 0).fold("") { text =>
      val lines = text.split("\n", -1).toList
      val starts = lines.scanLeft(0)(_ + _.length + 1)
      val k = starts.lastIndexWhere(_ <= n.at).min(lines.size - 1).max(0)
      def indent(l: String) = l.takeWhile(_ == ' ').length
      val Statement = """^\s*(?:(?:private|protected|final|lazy|override|inline)\s+)*(?:val|def|given|var)\b.*""".r
      // The statement holding the call: the nearest `val`/`def` above it, no deeper than its line...
      val from = (k to 0 by -1).find(j => lines(j).trim.nonEmpty && indent(lines(j)) <= indent(lines(k)) && Statement.matches(lines(j))).getOrElse(k)
      // ...to the next line as shallow as it that does not continue it (a closing bracket, a chained call;
      // a comment may sit between chained calls, and the comments before the next statement are not its).
      def comment(t: String) = Seq("//", "/*", "*").exists(t.startsWith)
      val to = ((from + 1) until lines.size).find { j =>
        val t = lines(j).trim
        t.nonEmpty && !comment(t) && indent(lines(j)) <= indent(lines(from)) && !Seq(")", "}", "]", ".").exists(t.startsWith)
      }.getOrElse(lines.size)
      val body = lines.slice(from, to).map(_.stripTrailing).reverse.dropWhile(l => l.isEmpty || comment(l.trim)).reverse
      // Dedented: moving the statement into or out of a block is not a change of what it says.
      val margin = body.filter(_.trim.nonEmpty).map(indent).minOption.getOrElse(0)
      body.map(_.drop(margin)).mkString("\n")
    }

  /** The section of the idea a node is decided against. */
  def ideaOf(n: Node[?]): String = ideaOfText(ideaDecided, n)

  private def ideaOfText(ideaDecided: String, n: Node[?]): String =
    Decisions.ideaSections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

  /** Sections of the idea no node is decided against, and nodes naming a section the idea does not have. */
  def ideaCoverage: List[String] =
    val named = kb.nodes.map(_.ideaSection.trim).filter(_.nonEmpty)
    val sections = Decisions.ideaSections(ideaDecided)._2.map(_._1)
    sections.filterNot(h => named.exists(_.equalsIgnoreCase(h)))
      .map(h => s"the section \"$h\" of ${kb.idea} is the concern of no node: name it on the node that states it (idea = \"$h\"), or move it to Not modelled") ++
      kb.nodes.filter(_.ideaSection.trim.nonEmpty).filterNot(n => sections.exists(_.equalsIgnoreCase(n.ideaSection.trim)))
        .map(n => s"${n.id} is decided against the section \"${n.ideaSection}\", which ${kb.idea} does not have")

  def hash(n: Node[?]): String = Decision.hash(content(n))

  /** The node's content together with what it rests on: a change of meaning anywhere above shows below.
    * What is not modelled is reviewed at the nodes that name it only: it narrows nothing below them.
    */
  def chainHash(n: Node[?]): String = chains(n, scala.collection.mutable.Map.empty)

  private def chains(n: Node[?], memo: scala.collection.mutable.Map[String, String]): String =
    memo.getOrElseUpdate(n.id, Decisions.chain(content(n), restChain(n, memo)))

  /** What a node rests on: the chains of its parents, of the definitions it uses and of the contracts its
    * code calls. A design decision rests on its parents' place, not their meaning; another knowledge
    * base's node, on what it rested on when decided there.
    */
  def parentChain(n: Node[?]): String = restChain(n, scala.collection.mutable.Map.empty)

  private def restChain(n: Node[?], memo: scala.collection.mutable.Map[String, String]): String =
    if kb.imports.contains(n.id) then ledger.binding(n.id).fold("")(_.chain)
    else if n.kind == NodeKind.Design then ""
    else Decisions.above("", restsOn(n).map(chains(_, memo)))

  /** The nodes a node rests on: its parents, the definitions it uses, and the contracts its code calls. */
  def restsOn(n: Node[?]): List[Node[?]] =
    (kb.parentsOf(n) ++ kb.definitionsUsed(n, generate.inForce) ++ generate.callees(n)).distinctBy(_.id)

  /** Files governed explicitly by some node. */
  private lazy val governedExplicitly: Set[Path] =
    kb.nodes.flatMap(_.governs).map(f => ws.root.resolve(f).toAbsolutePath.normalize).toSet

  /** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. It
    * covers the node's Lean, its proof file, the definitions it uses, its parts' and its callees' checks
    * (and, for the root, everything `root_impl` is composed of).
    */
  def checkHash(n: Node[?]): String =
    val (g, hashes) = cache
    def go(n: Node[?], seen: Set[String]): String = hashes.getOrElse(n.id, {
      val proof = read(ws.lean.resolve(g.proofsPath(n.id)))
      val h = sha((Seq(g.spec(n), g.auto(n), g.theorems(n), g.checks(n), g.evalFile(n).getOrElse(""), g.provenImpl(n).fold("")(_ => g.impl(n)),
        if kb.root.exists(_ eq n) then g.rootImpl.fold("")(_._2) else "",
        proof.getOrElse(""), proof.filter(Lean.lemmaImports(_).nonEmpty).flatMap(_ => read(ws.lean.resolve(g.lemmasPath))).getOrElse(""),
        // The specs of other nodes a proof imports: a change to them re-checks it.
        proof.fold("")(src => s"(?m)^\\s*import\\s+FrFlowGen\\.${java.util.regex.Pattern.quote(kb.name)}\\.(\\w+)\\.Spec".r
          .findAllMatchIn(src).map(_.group(1)).filter(_ != n.id).flatMap(kb.node).filter(g.formal).map(g.spec).mkString),
        (kb.parts(n) ++ g.callees(n) ++ (if kb.root.exists(_ eq n) then g.trusted ++ kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
          .filter(g.formal).distinctBy(_.id).filterNot(c => seen(c.id) || (c eq n)).map(go(_, seen + n.id)).mkString,
        Workflow.CheckerVersion.toString) ++ g.declarationsUsedBy(n))*)
      hashes(n.id) = h
      h
    })
    go(n, Set.empty)

  // ---------------------------------------------------------------------------
  // Check
  // ---------------------------------------------------------------------------

  /** Checks nodes (all, or one), parts first, and records the results. */
  def check(only: Option[String] = None, verify: Set[String] = Set.empty): List[(Node[?], NodeCheck)] =
    render()
    val lake = Lake(ws.lean)
    val g = generate
    val todo = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id))
    // A node proven again: its compiled modules are forgotten first, so Lean elaborates it, not a build cache.
    verify.flatMap(kb.node).foreach(forgetBuild)
    // A node is checked after what its Lean imports: its parts, and the contracts its code calls (the
    // root's `root_impl` imports every proven implementation); the nodes of one level side by side.
    val levels = scala.collection.mutable.Map.empty[String, Int]
    def level(n: Node[?], seen: Set[String]): Int = levels.getOrElse(n.id, {
      val below = (kb.parts(n) ++ g.callees(n) ++ (if kb.root.exists(_ eq n) then kb.nodes.filter(c => g.provenImpl(c).isDefined) else Nil))
        .filter(x => g.formal(x) && !seen(x.id) && !(x eq n))
      val l = below.map(level(_, seen + n.id) + 1).maxOption.getOrElse(0)
      levels(n.id) = l
      l
    })
    // A node whose formal parts did not change keeps its result (unless it is to be verified anew).
    def unchanged(n: Node[?]) = current(n).filter(_ => only.isEmpty && !verify(n.id))
    val pending = todo.filter(unchanged(_).isEmpty)
    // The models first, in one build Lake runs in parallel. A batch that builds is built for each of
    // its targets: their own builds are skipped (one at a time, they cost about as much as Lean's start).
    val built = java.util.concurrent.ConcurrentHashMap.newKeySet[String]()
    def batch(targets: Seq[String]): Unit =
      if targets.size > 1 && lake.buildAll(targets).ok then targets.foreach(built.add)
    batch(pending.filter(g.waitsForDefinition(_).isEmpty).map(n => g.specModule(n.id)))
    val threads = sys.env.get("FRFLOW_THREADS").flatMap(_.toIntOption).getOrElse(Runtime.getRuntime.availableProcessors.min(4)).max(1)
    val pool = java.util.concurrent.Executors.newFixedThreadPool(threads)
    val done = scala.collection.concurrent.TrieMap.empty[String, NodeCheck]
    try todo.groupBy(level(_, Set.empty)).toList.sortBy(_._1).foreach { (_, ns) =>
      // A level's theorems in one build, which Lake runs in parallel (builds are one at a time).
      batch(ns.filter(n => unchanged(n).isEmpty && g.waitsForDefinition(n).isEmpty).map(n => g.theoremsModule(n.id)))
      ns.map { n =>
        val partStatus = kb.parts(n).filter(g.formal).map(p => p.id -> done.get(p.id).orElse(current(p)).map(_.status).getOrElse("not-checked"))
        n -> pool.submit(() => unchanged(n).getOrElse(checkNode(n, g, lake, partStatus, built.contains)))
      }.foreach((n, f) => done(n.id) = f.get())
    }
    finally pool.shutdown()
    val results = todo.map(n => n -> done(n.id))
    val kept = checks.filter((id, _) => kb.node(id).isDefined)
    val all = results.foldLeft(kept)((m, r) => m.updated(r._1.id, r._2))
    Checks.save(ws.checksFile, all)
    synchronized { checksCache = None }
    results

  /** Removes what Lake built of a node (its model, theorems, proof), so that it is elaborated again. */
  private def forgetBuild(n: Node[?]): Unit =
    val build = ws.lean.resolve(".lake/build")
    val k = kb.name
    if Files.isDirectory(build) then
      val mine = (p: Path) =>
        val u = build.relativize(p).toString.replace('\\', '/')
        u.contains(s"FrFlowGen/$k/${n.id}/") || u.matches(s".*Proofs/$k/${java.util.regex.Pattern.quote(n.id)}\\.[^/]+")
      scala.util.Using.resource(Files.walk(build))(_.iterator.asScala.toList).filter(p => Files.isRegularFile(p) && mine(p)).foreach(Files.delete)

  /** Some of the results recorded and still current, chosen at random (at least one when there are
    * any): `ci` proves them again, so a cache that says "proven" of what Lean no longer proves is found.
    */
  def sample(fraction: Double, seed: Long = System.nanoTime): Set[String] =
    val cached = kb.nodes.filter(n => generate.formal(n) && current(n).exists(_.status == "proven")).map(_.id)
    if cached.isEmpty || fraction <= 0 then Set.empty
    else scala.util.Random(seed).shuffle(cached).take((cached.size * fraction).ceil.toInt.max(1)).toSet

  private def checkNode(n: Node[?], g: Generate, lake: Lake, partStatus: List[(String, String)], built: String => Boolean = _ => false): NodeCheck =
    def build(target: String) = if built(target) then Run(0, "") else lake.build(target)
    // The examples, evaluated in Lean: every result carries them.
    var evaluated: List[Result] = Nil
    def done(status: String, rs: List[Result], msgs: List[String], axioms: List[String] = Nil) =
      NodeCheck(checkHash(n), status, rs ++ evaluated, msgs, axioms, java.time.Instant.now.toString)
    def errors(r: Run) =
      val ds = Lean.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
      if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))
    def timedOut(r: Run) = !r.ok && r.output.contains("timed out after")

    // Two definitions of a term it uses, neither chosen: what it says is not known yet.
    val waits = g.waitsForDefinition(n)
    if waits.nonEmpty then return done("waiting", Nil, List(s"waits for the choice between the definitions of ${waits.mkString(", ")} (${waits.flatMap(t => kb.definitionsOf(t).map(_.id)).mkString(", ")})"))

    val spec = build(g.specModule(n.id))
    // A timeout is not a broken model: the machine was busy, or Lean slow; it is checked again.
    if timedOut(spec) then return done("timeout", Nil, List("Lean timed out building the model (the machine may be busy): run check again"))
    if !spec.ok then return done("model-error", Nil, errors(spec))

    // Lemmas shared by the proof files: the same filter, built.
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

    // Scala and Lean must agree on every example: what Scala computes of it, Lean proves; its
    // opposite, Lean does not. A disagreement means the translation does not mean what the Scala does,
    // and nothing proven of the node is about the code.
    val (evals, notEvaluated) = g.evals(n)
    if evals.nonEmpty then
      val rel = g.evalPath(n.id)
      val run = lake.elaborate(rel)
      val decls = Lean.theorems(read(ws.lean.resolve(rel)).getOrElse(""))
      val diags = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
      def proves(name: String) = decls.find(_.name == name).exists(d => !diags.exists(x => x.isError && x.line >= d.from && x.line <= d.to))
      evaluated = evals.map { e =>
        (proves(e.name), proves(e.name + "_opposite")) match
          case _ if diags.isEmpty && !run.ok => Result(e.name, "unevaluated", s"${e.what}: Lean did not run: ${run.output.take(20000)}")
          case (true, false) => Result(e.name, "proven", s"Lean agrees: ${e.claim}")
          case (false, true) => Result(e.name, "failed", s"${e.what}: Scala computes ${e.claim}, Lean proves ${e.opposite}")
          case (true, true)  => Result(e.name, "failed", s"${e.what}: Lean proves both ${e.claim} and its opposite")
          case (false, false) => Result(e.name, "unevaluated", s"${e.what}: Lean decides neither ${e.claim} nor its opposite")
      }.filterNot(r => r.name.startsWith("probe") && r.status == "unevaluated") // a probe Lean cannot decide says nothing
    evaluated ++= notEvaluated.map((name, why) => Result(name, "unevaluated", why))
    val disagree = evaluated.filter(_.status == "failed")
    if disagree.nonEmpty then return done("failed", Nil,
      s"Lean and Scala disagree on ${disagree.size} example(s) or probe(s): the Lean translation does not mean what the Scala does, so nothing proven of ${n.id} is about the code" :: disagree.map(_.detail))

    // A theorem of a file: proven when Lean reports no error in it and no `sorry`; an authored one must
    // state exactly its obligation and use only what a proof file may.
    def judge(name: String, rel: String, run: Run, isAuthored: Boolean): Result =
      val src = read(ws.lean.resolve(rel)).getOrElse("")
      val diags = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
      Lean.theorems(src).find(_.name == name) match
        case None => Result(name, "open", s"no theorem $name in $rel")
        case Some(d) =>
          def in(l: Int) = l >= d.from && l <= d.to
          val bad = if isAuthored then Lean.violations(src) else Nil
          if d.statement != s"Obl.$name" then Result(name, "failed", s"must state exactly Obl.$name")
          else if bad.nonEmpty then Result(name, "failed", s"not allowed in a proof file: ${bad.map(_._2).distinct.mkString(", ")}")
          else diags.find(x => x.isError && in(x.line)) match
            case Some(err) => Result(name, "open", err.message.take(20000))
            case None if diags.exists(x => x.isSorry && in(x.line)) => Result(name, "open", "uses sorry")
            case None if !run.ok => Result(name, "open", "not checked: " + run.output.take(20000))
            case None => Result(name, "proven", if isAuthored then "authored" else "auto")

    // Its parts make it: built already (with its level), automatic `complete` is proven without elaborating it again.
    val split = g.obligation(n, "complete").toList.map { o =>
      val prebuilt = Option.when(!authored(n.id))(build(g.theoremsModule(n.id))).filter(_.ok)
      if prebuilt.isDefined then Result(o.name, "proven", "auto")
      else
        val rel = if authored(n.id) then g.proofsPath(n.id) else g.autoPath(n.id)
        judge(o.name, rel, lake.elaborate(rel), authored(n.id))
    }
    // Its code meets it, from what the contracts it calls promise.
    var implAxioms: List[String] = Nil
    val implemented = g.obligation(n, "impl").toList.map { o =>
      val auth = g.isAuthored(n, "impl")
      if auth then
        val bad = Lean.violations(proofSrc)
        val stated = Lean.theorems(proofSrc).find(_.name == "impl").map(_.statement)
        if bad.nonEmpty then Result("impl", "failed", s"not allowed in a proof file: ${bad.map(_._2).distinct.mkString(", ")}")
        else if !stated.contains("Obl.impl") then Result("impl", "failed", "must state exactly Obl.impl")
        else
          val run = lake.build(g.implModule(n.id))
          implAxioms = Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List("<no audit result>"))
          if run.ok && !implAxioms.contains("sorryAx") then Result("impl", "proven", "authored")
          else if run.ok then Result("impl", "open", "uses sorry")
          else Result("impl", "open", s"not proven (authored): " + errors(run).take(3).mkString("\n").take(20000))
      else
        val run = lake.build(g.implModule(n.id))
        implAxioms = Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List("<no audit result>"))
        if run.ok then Result("impl", "proven", "auto")
        else Result("impl", "open", s"not proven (auto): prove theorem impl : Obl.impl in lean/${g.proofsPath(n.id)}\nLean: " + errors(run).take(3).mkString("\n").take(20000))
    }
    val results = split ++ implemented
    if results.exists(_.status == "failed") then return done("failed", results, Nil)
    if split.exists(_.status == "open") then
      return done("open", results, List(s"prove it in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)"))
    val notYet = partStatus.filter(_._2 != "proven")
    if notYet.nonEmpty then return done("waiting", results, List(s"waiting for its parts: ${notYet.map(_._1).mkString(", ")}"))

    val thms = build(g.theoremsModule(n.id))
    if timedOut(thms) then return done("timeout", results, List("Lean timed out building the node's theorems: run check again"))
    if !thms.ok then return done("failed", results, "the node's theorems do not build" :: errors(thms))
    // The proof file, when it proves obligations of the Checks file.
    val proofFile: Option[String] =
      if !g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) then None
      else
        val bad = Lean.violations(proofSrc)
        if bad.nonEmpty then Some(s"not allowed in lean/${g.proofsPath(n.id)}: ${bad.map(_._2).distinct.mkString(", ")}")
        else
          val built = lake.build(g.proofsModule(n.id))
          Option.when(!built.ok)(s"lean/${g.proofsPath(n.id)} does not build: " + errors(built).take(5).map(_.take(20000)).mkString("\n"))
    // Everything else imports it: what it proves fails, by name, and the file is the message.
    if proofFile.isDefined then return done("failed",
      results ++ g.extraObligations(n).filter(o => g.isAuthored(n, o.name)).map(o => Result(o.name, "failed", proofFile.get)), List(proofFile.get))
    // Everything else, in one run of Lean (see `Generate.checks`): each theorem holds when Lean reports
    // no error in it, no `sorry`, and its axioms (fail closed: no audit, no proof).
    def elaborated(rel: String): (Run, String => Option[String], String => Option[List[String]]) =
      val run = lake.elaborate(rel)
      val decls = Lean.theorems(read(ws.lean.resolve(rel)).getOrElse(""))
      val diags = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
      val ax = Lean.axioms(run.output)
      def axiomsOf(name: String) = ax.collectFirst { case (t, as) if t == name || t.endsWith("." + name) => as }
      def why(name: String): Option[String] = decls.find(_.name == name) match
        case None => Some(s"no theorem $name")
        case Some(d) =>
          def in(l: Int) = l >= d.from && l <= d.to
          diags.find(x => x.isError && in(x.line)).map(_.message.linesIterator.filterNot(_.contains("depends on axioms")).mkString("\n").take(20000))
            .orElse(Option.when(diags.exists(x => x.isSorry && in(x.line)) || axiomsOf(name).exists(_.contains("sorryAx")))("uses sorry"))
      (run, why, axiomsOf)
    val rel = g.checksPath(n.id)
    val (run, why, axiomsOf) = elaborated(rel)
    if timedOut(run) then return done("timeout", results, List("Lean timed out checking the node (the machine may be busy): run check again"))
    def holds(name: String) = why(name).isEmpty
    // The tries: what Lean proves of them says the node or its split says nothing, or too much.
    val tried = g.tries(n).map(t => (t, holds(t.obligation.name)))
    val fatal = tried.collect { case (t, true) if Set("unsat", "clash")(t.obligation.name) => t.means }
    val tryResults = tried.map { (t, proven) =>
      val name = t.obligation.name
      if name == "idle" then Result("idle", if proven then "proven" else "open", g.idleWhat(n))
      else if name.startsWith("vacuous_expect_") then Result(name, if proven then "failed" else "proven", if proven then t.means else "")
      else if name == "unsat" || name == "clash" then Result(name, if proven then "failed" else "proven", if proven then t.means else "not shown")
      else Result(name, if proven then "open" else "proven", if proven then t.means else "needed: Lean does not show the node without it")
    }
    val extra = g.extraObligations(n).map { o =>
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      if o.name.startsWith("expect_") && tried.exists((t, p) => p && t.obligation.name == s"vacuous_${o.name}") then
        (Result(o.name, "failed", "it holds whatever the node says: it checks nothing"), Nil)
      else why(o.name) match
        case None => (Result(o.name, "proven", how), axiomsOf(o.name).getOrElse(List("<no audit result>")))
        case Some("uses sorry") => (Result(o.name, "open", "uses sorry"), Nil)
        case Some(w) => (Result(o.name, "open", s"not proven ($how): prove theorem ${o.name} : Obl.${o.name} in lean/${g.proofsPath(n.id)}\nLean: $w"), Nil)
    }
    // A view whose coverage cannot be stated keeps nothing proven.
    val uncovered = g.formalKeeps(n).flatMap((i, _) => g.coverage(n, i).left.toOption.map(w =>
      Result(s"cover_${i.id}", "failed", s"what the view must list cannot be stated: $w")))
    // The root, of the code: from what is trusted only.
    val (rootImpl, rootAxioms) = g.rootImpl.filter(_ => kb.root.exists(_ eq n)).fold((List.empty[Result], List.empty[String])) { _ =>
      val (rrun, rwhy, raxioms) = elaborated(g.rootImplPath)
      rwhy("root_impl") match
        case None => (List(Result("root_impl", "proven", s"the root holds of the code, trusting ${if g.trusted.isEmpty then "nothing" else g.trusted.map(_.id).mkString(", ")}")),
          raxioms("root_impl").getOrElse(List("<no audit result>")))
        case Some(w) => (List(Result("root_impl", "open", s"the root is not proven of the code: $w${if rrun.ok then "" else "\n" + errors(rrun).take(3).mkString("\n").take(5000)}")), Nil)
    }
    val used = (axiomsOf("holds").getOrElse(List("<no audit result>")) ++ extra.flatMap(_._2) ++ (if implemented.exists(_.status == "proven") then implAxioms else Nil) ++
      rootAxioms).distinct.sorted
    val all = results ++ extra.map(_._1) ++ uncovered ++ tryResults ++ rootImpl
    if fatal.nonEmpty then done("failed", all, fatal, used)
    else if used.contains("<no audit result>") then
      done("failed", all, List(s"Lean did not finish checking lean/$rel: " + errors(run).take(3).map(_.take(5000)).mkString("\n")), used)
    else if used.exists(a => !Lean.allowedAxioms(a)) then done("failed", all, List(s"disallowed axioms: ${used.filterNot(Lean.allowedAxioms).mkString(", ")}"), used)
    // (What is left open is in the results, once: not repeated as messages.)
    else done("proven", all, Nil, used)

  /** The recorded check of a node, if still current. */
  def current(n: Node[?]): Option[NodeCheck] =
    // A result that waited, or timed out, is not final: it is checked again.
    if !generate.formal(n) then None else checks.get(n.id).filter(c => c.hash == checkHash(n) && !Set("waiting", "timeout", "model-error")(c.status))

  /** The source files a node governs: a contract's implementation, a design decision's files. */
  def code(n: Node[?]): Option[Code] =
    // An implementation governs the files of the code its expression refers to (not the model's
    // file); anything else it depends on is governed explicitly (a design node owning a
    // directory), or `status` reports it as governed by no node.
    val impl = kb.implementation(n).toList.flatMap { i =>
      i.sources.filterNot(kb.modelFiles.contains).map(f => Path.of(f).toAbsolutePath.normalize)
        .filterNot(p => governedExplicitly.exists(g => p == g || p.startsWith(g)))
    }
    // Another knowledge base's code, as its project names it.
    val base = kb.imports.get(n.id).fold(ws.root)(i => ws.root.resolve(i.root).normalize)
    val files = n.governs.map(base.resolve) ++ impl
    if files.isEmpty then None else Some(Code.of(base, files))

  /** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`, each with a
    * status (`proven`, `open`, `failed`, `unchecked`, `timeout`, `informal`) and a detail. Null for a node
    * with no parts.
    */
  def split(n: Node[?]): Json =
    def st(status: String, detail: String) = obj("status" -> str(status), "detail" -> str(detail))
    val parts = kb.parts(n)
    if parts.isEmpty || !kb.isStatement(n) then JNull
    else if generate.splitParts(n).isEmpty then
      val informal = st("informal", "not formalized: decided by reading")
      obj("complete" -> informal, "needed" -> JArr(parts.map(p => JObj(("id" -> str(p.id)) +: informal.obj))), "clash" -> informal)
    else current(n) match
      case None =>
        val c = checks.get(n.id)
        val why = c.filter(_.status == "waiting").flatMap(_.messages.headOption).orElse(c.filter(_.status == "timeout").map(_ => "Lean timed out: run check again"))
          .getOrElse(if c.isDefined then "changed since the last check" else "not checked yet")
        val un = st(if c.exists(_.status == "timeout") then "timeout" else if c.exists(_.status == "model-error") then "failed" else "unchecked",
          if c.exists(_.status == "model-error") then "the model does not build: " + c.get.messages.headOption.getOrElse("") else why)
        obj("complete" -> un, "needed" -> JArr(parts.map(p => JObj(("id" -> str(p.id)) +: un.obj))), "clash" -> un)
      case Some(c) =>
        def res(name: String) = c.obligations.find(_.name == name)
        val complete = res("complete") match
          case Some(r) if r.status == "proven" && c.obligations.exists(o => o.name == "feasible" && o.status != "proven") =>
            st("open", "its parts make it by an authored proof: prove `feasible` too (some world meets the parts), or give a proven implementation below")
          case Some(r) => st(r.status, r.detail.linesIterator.nextOption().getOrElse(""))
          case None => st("failed", c.messages.headOption.getOrElse("the check failed"))
        val needed = parts.map(p => JObj(("id" -> str(p.id)) +: (res(if parts.size == 1 then "vacuous" else s"needed_${p.id}")
          .fold(st("unchecked", "not checked"))(r => st(r.status, r.detail)).obj)))
        obj("complete" -> complete, "needed" -> JArr(needed), "clash" -> res("clash").fold(st("unchecked", "not checked"))(r => st(r.status, r.detail)))

  // ---------------------------------------------------------------------------
  // Decisions
  // ---------------------------------------------------------------------------

  /** Applies a decision (see `Decisions.decide`) to a fresh snapshot and records it: for programs and
    * tests. The browser decides through `tools.Project`, on the snapshot the developer saw.
    */
  def decide(r: Decisions.Request): Either[String, Unit] =
    val files = kb.nodes.flatMap(code).flatMap(_.files).distinct
    Decisions.decide(baseSnapshot, ledger, r, java.time.Instant.now.toString, Git.head(ws.root), Git.snapshot(ws.root, files))
      .map(l => Ledger.save(ws.ledgerFile, Ledger(l.decisions -- kb.imports.keySet)))

  /** Warnings about the record (decisions not signed by the developer) and the code. */
  def integrity: List[String] = Ledger.warnings(ws.ledgerFile, Ledger.load(ws.ledgerFile)) ++ ownerWarnings ++ importWarnings ++ codeWarnings

  /** Decisions in a concern with an owner made by someone else (with named keys, `by` is the key's name). */
  /** Who decides a node: its own owner, else its first parent's, recursively; none, anyone. */
  def ownerOf(n: Node[?]): String =
    def go(x: Node[?], seen: Set[String]): String =
      if x.owner.nonEmpty || seen(x.id) then x.owner else kb.parentsOf(x).headOption.fold("")(go(_, seen + x.id))
    go(n, Set.empty)

  /** Decisions on an owned node made by someone else (with named keys, `by` is the key's name). */
  private def ownerWarnings: List[String] =
    val own = Ledger.load(ws.ledgerFile)
    kb.nodes.filterNot(n => kb.imports.contains(n.id)).flatMap { n =>
      val owner = ownerOf(n)
      if owner.isEmpty then Nil
      else own.decisions.getOrElse(n.id, Nil).filter(d => d.action != "revisit" && !d.by.trim.equalsIgnoreCase(owner))
        .map(d => s"${n.id}: the ${d.action} of ${d.at} is by ${d.by}, but $owner owns it: $owner decides it again")
    }

  /** Decisions of another knowledge base's nodes, checked against its own keys. */
  private def importWarnings: List[String] =
    kb.imports.groupBy(_._2).toList.flatMap { (imp, ids) =>
      val dir = ws.root.resolve(imp.root).normalize
      val theirs = Ledger.load(dir.resolve(".frflow/ledger.json"))
      val mine = Ledger(theirs.decisions.filter((id, _) => ids.contains(id)))
      Signing.unsigned(mine, dir.resolve(".frflow/keys")).map((id, d) =>
        s"$id (decided in ${imp.kb}): the ${d.action} of ${d.at} by ${d.by} is not signed by one of ${imp.kb}'s developer keys")
    }

  /** Warnings about the model and the code (the ledger's are read live, see `Ledger.warnings`). */
  def codeWarnings: List[String] =
    val missing = kb.nodes.flatMap(n => n.governs.filterNot(f => Files.exists(ws.root.resolve(f))).map(f => s"${n.id} governs $f, which does not exist"))
    // One owner per file: two nodes governing it would each review it as its own.
    val owners = kb.nodes.flatMap(n => code(n).toList.flatMap(_.files).map(_ -> n.id)).groupBy(_._1).toList.sortBy(_._1)
      .collect { case (f, ns) if ns.map(_._2).distinct.size > 1 => s"$f is governed by ${ns.map(_._2).distinct.mkString(" and ")}: give it one owner" }
    // A proof file of no node (after a rename or a removal) proves nothing any more.
    val proofsDir = ws.lean.resolve(s"Proofs/${kb.name}")
    val orphans = if !Files.isDirectory(proofsDir) then Nil
      else Files.list(proofsDir).iterator.asScala.map(_.getFileName.toString).filter(_.endsWith(".lean")).map(_.stripSuffix(".lean"))
        .filterNot(id => id == "Lemmas" || kb.node(id).isDefined).toList.sorted
        .map(id => s"lean/Proofs/${kb.name}/$id.lean is the proof file of no node: move it with its node's new id (and its namespace), or remove it")
    missing ++ owners ++ ideaCoverage ++ staleNames ++ orphans ++ modelCode ++ bypasses ++
      ungoverned.map(f => s"$f is governed by no node: govern it (a design node) or move it")

  /** Wiring that calls a contract's code directly, past `service` (so what it returns is not
    * checked): a file a design node governs naming a method the registered code calls.
    */
  def bypasses: List[String] =
    val wired = kb.nodes.filter(_.kind == NodeKind.Design).flatMap(d => code(d).toList.flatMap(_.files)).distinct
    adapters.flatMap { (c, i, files) =>
      val called = """\.(\w+)\(""".r.findAllMatchIn(i.wiring).map(_.group(1)).toSet
      // An adapter's methods that change the outside: those returning Unit.
      val effects = files.flatMap(f => read(ws.root.resolve(f)).toList.flatMap(Workflow.methods).filter(_.unit).map(m => m.name -> f))
      wired.filterNot(files.contains).flatMap(f => read(ws.root.resolve(f)).toList.flatMap { text =>
        def calls(m: String) = s"\\.$m\\(".r.findFirstIn(text).isDefined
        called.toList.sorted.filter(calls).map(m => s"$f calls ${c.id}'s code directly (.$m): go through service(${c.id}), so what it returns is checked") ++
          effects.filter((m, _) => calls(m)).map((m, af) => s"$f changes the outside directly (.$m, in $af): go through an assumption on an operation, so the change is checked")
      })
    }.distinct

  /** The ports' adapters: the contract, its implementation with production code, and the files that code is in. */
  private def adapters: List[(Node[?], Implementation, List[String])] =
    val model = kb.modelFiles.map(f => ws.root.resolve(f).toAbsolutePath.normalize).toSet
    kb.nodes.flatMap(c => kb.implementation(c).filter(_.wiring.nonEmpty).map(i =>
      (c, i, code(c).toList.flatMap(_.files).filterNot(f => model(ws.root.resolve(f).toAbsolutePath.normalize)))))

  /** What doing nothing is, when it meets the node (Lean proved it). */
  /** What doing nothing is, when it meets the root (Lean proved it). */
  def idleOf(n: Node[?]): Option[String] = current(n).flatMap(_.obligations.find(o => o.name == "idle" && o.status == "proven")).map(_.detail)

  /** Top-level code in a model file that is none of the model (a node, a `define`, an open term, a type,
    * the knowledge base, a `@main`): it would run unseen by any node, next to the model.
    */
  def modelCode: List[String] =
    val ValName = """^\s*(?:lazy\s+)?val\s+([A-Za-z_]\w*)""".r.unanchored
    val known = (kb.nodes.flatMap(n => ValName.findFirstMatchIn(definition(n)).map(_.group(1))) ++ kb.defs.map(_.name) ++
      kb.params.map(_.name) ++ kb.opaques.map(_.name)).toSet
    val Top = """^(?:(?:private|protected|final|lazy|implicit|inline|override|abstract)\s+)*(val|var|def|object|class|given|extension)\b\s*([A-Za-z_]\w*)?(.*)$""".r
    kb.modelFiles.distinct.flatMap { f =>
      read(Path.of(f)).orElse(read(ws.root.resolve(f))).toList.flatMap(_.linesIterator.zipWithIndex.collect {
        case (Top(kw, name, rest), i) if !(kw == "val" && (known(Option(name).getOrElse("")) ||
            Seq("= KnowledgeBase(", "= define", "= Opaque(", "= Param[", "= Param(").exists(rest.trim.startsWith) ||
            rest.contains("KnowledgeBase") || Workflow.isData(rest))) =>
          s"${Path.of(f).getFileName}:${i + 1}: `$kw ${Option(name).getOrElse("")}` is code in the model's file that no node governs: make it a `define` (proven), or move it to a governed file"
      })
    }

  /** Statements and reasons that name a node no longer chosen (rejected, or removed): the text
    * still rests on it.
    */
  def staleNames: List[String] =
    val l = ledger
    val ids = kb.nodes.map(_.id).toSet
    val dropped = l.decisions.keySet.filter(id =>
      (l.current(id).exists(_.action == "remove") || l.current(id).exists(_.action == "reject"))).toSet
    kb.nodes.filterNot(n => l.current(n.id).exists(_.action == "reject")).flatMap { n =>
      dropped.toList.sorted.filter(d => d != n.id && s"\\b${java.util.regex.Pattern.quote(d)}\\b".r.findFirstIn(n.statement + " " + n.why).isDefined)
        .map(d => s"${n.id}: its statement or why names $d, which is ${if ids(d) then "rejected" else "removed"}")
    }

  /** Source files no node governs, other than the model's own: code that can change unnoticed. They
    * are every file under `src/main`, every source file elsewhere in the project (but tests, builds'
    * output, the Lean and FrFlow's own records), and every source the build compiles, when the build
    * names them (`-Dfrflow.sources`, as the examples' build does): a source directory added in the
    * build is production code too.
    */
  def ungoverned: List[String] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(ws.root)
    val governed = kb.nodes.flatMap(code).flatMap(_.files).map(f => abs(ws.root.resolve(f))).toSet ++
      kb.modelFiles.map(f => abs(Path.of(f)))
    // The file that puts the knowledge base together (its concerns listed) is the model's too.
    def assembles(p: Path) = read(p).exists(_.contains("KnowledgeBase(\""))
    projectSources.filterNot(p => governed(p) || assembles(p)).map(p => if p.startsWith(root) then root.relativize(p).toString else p.toString).sorted

  /** The project's source files (see `ungoverned`). */
  def projectSources: List[Path] =
    val abs = (p: Path) => p.toAbsolutePath.normalize
    val root = abs(ws.root)
    // Only the project's own output and records are skipped, at its root: a `target` folder inside the
    // sources is compiled like any other.
    // The build's own definitions (`project/*.scala`, `*.sbt`) are code too: only their output is skipped.
    val skipDirs = Set("target", "lean", ".frflow", "node_modules")
    val codeExt = Set("scala", "sc", "sbt", "java", "kt", "js", "ts", "py", "go", "rs", "sql", "sh")
    def walk(dir: Path): List[Path] =
      if !Files.isDirectory(dir) then Nil
      else Files.list(dir).iterator.asScala.toList.flatMap { p =>
        val name = p.getFileName.toString
        if Files.isDirectory(p) then
          val parent = abs(p).getParent
          // Hidden directories are code like any other, but the tools' own at the root (.git, .bsp, ...).
          if (name.startsWith(".") && parent == root) || (skipDirs(name) && parent == root) || root.relativize(abs(p)).toString == "src/test" ||
            ((name == "target" || name == "project") && parent == root.resolve("project")) then Nil else walk(p)
        else if root.relativize(abs(p)).startsWith("src/main") || codeExt(name.reverse.takeWhile(_ != '.').reverse) then List(p)
        else Nil
      }
    val fromBuild = sys.props.get("frflow.sources").toList.flatMap(_.split(java.io.File.pathSeparator)).filter(_.nonEmpty)
      .map(Path.of(_)).filterNot(p => abs(p).startsWith(root.resolve("target")))
    (walk(root) ++ fromBuild).filter(Files.isRegularFile(_)).map(abs).distinct

  /** Where the developer stands on each node (see `Decisions`). */
  def state(n: Node[?]): String =
    annotated("nodes").get.arr.find(_("id").flatMap(_.str).contains(n.id)).flatMap(_("state")).flatMap(_.str).get

  def gone: List[String] = annotated("gone").get.arr.flatMap(_("id").flatMap(_.str)).toList

  /** Creates the proof file of a node with a stub for its obligation. */
  def scaffold(n: Node[?]): Boolean =
    val g = generate
    val path = ws.lean.resolve(g.proofsPath(n.id))
    // The obligations the last check left open (`complete`, the implementation, a check...), or
    // `complete` before any check: a stub each, added to the proof file (created if missing).
    val names = g.obligations(n).map(_.name)
    val open = checks.get(n.id).toList.flatMap(_.obligations).filter(r => Set("open", "failed")(r.status)).map(_.name).filter(names.contains)
    val wanted = if open.nonEmpty then open else g.obligation(n, "complete").map(_.name).toList
    val existing = read(path).fold(List.empty[String])(src => Lean.theorems(src).map(_.name))
    val add = wanted.filterNot(existing.contains)
    if add.isEmpty then false
    else read(path) match
      case None => write(path, g.proofFile(n, add))
      case Some(src) =>
        val end = s"end ${kb.name}.${n.id}.Proofs"
        val i = src.lastIndexOf(end)
        if i < 0 then false else write(path, src.substring(0, i) + g.stubs(add) + src.substring(i))

  def tree(mark: Option[String] = None): String = Decisions.tree(annotated, mark)

  /** The tree and its warnings, and whether the knowledge base is complete (the CI gate). */
  def status: (String, Boolean) =
    val a = annotated
    val warnings = integrity ++ uncrossed
    val ok = Decisions.complete(a) && warnings.isEmpty
    // What each invariant does not reach (by the type of what a contract returns), so a gap is seen.
    val notes = kb.nodes.filter(_.isInvariant).flatMap { i =>
        val out = kb.nodes.filter(c => c.kind == NodeKind.Contract && !kb.inScope(i).contains(c))
        Option.when(out.nonEmpty)(s"${i.id} does not reach ${out.map(c => s"${c.id} (returns ${c.post.flatMap(_.params.lastOption).fold("?")(_._2)})").mkString(", ")}: its rule is about none of what they return")
      } ++
      // Without the merge driver, git merges the ledger as text, and a conflict resolved by hand can drop decisions.
      Option.when(Files.isRegularFile(ws.ledgerFile) && Git.head(ws.root).nonEmpty && Git.config(ws.root, "merge.frflow-ledger.driver").isEmpty)(
        "the ledger's merge driver is not set in this clone: git config merge.frflow-ledger.driver \"bin/frflow merge-ledger %O %A %B\"")
    (Decisions.tree(a) + "\n\n" + trustedLine + coverage + "\n" + Decisions.load(a) + notes.map("note: " + _ + "\n").mkString + warnings.map("warning: " + _ + "\n").mkString +
      (if ok then "Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass."
       else "Not every node is accepted, proven, and passing its examples, or there are warnings.") + "\n", ok)

  /** What the root rests on, of the code: the hypotheses of `root_impl`. */
  def trustedLine: String =
    val g = generate
    kb.root.filter(g.formal).fold("") { r =>
      val st = current(r).flatMap(_.obligations.find(_.name == "root_impl")).fold("not checked")(_.status)
      s"Trusted (the hypotheses of root_impl, $st): ${if g.trusted.isEmpty then "nothing" else g.trusted.map(t => s"${t.id} (${Workflow.kindName(t)})").mkString(", ")}.\n"
    }

  /** How far the proofs reach: splits proven, splits out of Lean, and contracts whose code is
    * proven, checked on examples only, or missing. What the experiment measures.
    */
  def coverage: String =
    val splits = kb.nodes.filter(n => kb.isStatement(n) && kb.parts(n).nonEmpty)
    def fine(j: Json) = j("status").flatMap(_.str).exists(Set("proven", "informal"))
    def provenSplit(n: Node[?]) =
      val s = split(n)
      s("complete").exists(c => c("status").flatMap(_.str).contains("proven")) && s("needed").exists(_.arr.forall(fine)) && s("clash").exists(fine)
    val formalSplits = splits.filter(n => generate.splitParts(n).isDefined)
    val proven = formalSplits.filter(provenSplit)
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    val code = provenCode
    val plain = contracts.filter(c => kb.implementation(c).exists(_.proven.isEmpty))
    val beside = contracts.filter(c => kb.implementation(c).exists(i => i.proven.isDefined && !i.provenCode))
    val designs = kb.nodes.filter(_.kind == NodeKind.Design)
    s"Proofs: ${proven.size} of ${splits.size} splits proven in Lean" +
      s"${if formalSplits.diff(proven).nonEmpty then s" (${formalSplits.diff(proven).map(_.id).mkString(", ")} not proven yet)" else ""}" +
      s"${if splits.diff(formalSplits).nonEmpty then s" (${splits.diff(formalSplits).map(_.id).mkString(", ")} out of Lean)" else ""}; " +
      s"code proven to meet its contract for ${code.size} of ${contracts.size} contracts" +
      (if plain.nonEmpty then s", checked on examples only for ${plain.map(_.id).mkString(", ")}" else "") +
      (if beside.nonEmpty then s", and of a proven define the code is checked against for ${beside.map(_.id).mkString(", ")}" else "") +
      (if designs.nonEmpty then s"; ${designs.size} design decision(s) govern code no proof covers (${designs.map(_.id).mkString(", ")})" else "") +
      evaluated + ".\n" + lines

  private def lines: String =
    def count(f: String) = read(ws.root.resolve(f)).fold(0)(_.linesIterator.count(_.trim.nonEmpty))
    val provenDefs = Def.closure(kb.nodes.flatMap(c => kb.implementation(c).filter(_.provenCode).flatMap(_.proven)))
    val proven = provenDefs.map(_.lifted.source.linesIterator.count(_.trim.nonEmpty)).sum
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    // Plain implementations: their files. Production code beside a proven define: only the adapter's
    // methods it calls (and the private ones they call), not the rest of the adapter's file.
    val plain = contracts.filter(c => kb.implementation(c).exists(i => !i.provenCode && i.wiring.isEmpty)).flatMap(c => code(c).toList.flatMap(_.files)).distinct
    val adapted = adapters.flatMap((_, i, files) => files.map(f => f -> """\.(\w+)""".r.findAllMatchIn(i.wiring).map(_.group(1)).toSet))
      .groupMapReduce(_._1)(_._2)(_ ++ _).toList.filterNot((f, _) => plain.contains(f))
    val checkedFiles = plain ++ adapted.map(_._1)
    val reviewedFiles = kb.nodes.filter(_.kind == NodeKind.Design).flatMap(d => code(d).toList.flatMap(_.files)).distinct.filterNot(checkedFiles.contains)
    val checked = plain.map(count).sum + adapted.map((f, names) => read(ws.root.resolve(f)).fold(0)(t => Workflow.linesOf(t, names))).sum
    val reviewed = reviewedFiles.map(count).sum
    if proven + checked + reviewed == 0 then ""
    else s"Code: $proven line(s) proven (define), $checked checked by running (plain implementations), $reviewed reviewed only (${reviewedFiles.size} file(s) design nodes govern).\n"

  /** How many examples Lean evaluated as Scala does (the translation's cross-check), and where none. */
  private def evaluated: String =
    val per = kb.nodes.filter(c => c.post.isDefined && generate.formal(c) && c.cases.nonEmpty).map { c =>
      val rs = current(c).toList.flatMap(_.obligations)
      (c, rs.count(o => o.name.startsWith("eval_") && o.status == "proven"), c.cases.size)
    }
    val probes = kb.nodes.flatMap(c => current(c).toList.flatMap(_.obligations)).count(o => o.name.startsWith("probe") && o.status == "proven")
    if per.isEmpty then ""
    else
      val none = per.filter((_, ok, _) => ok == 0).map(_._1.id)
      s"; examples evaluated in Lean as in Scala: ${per.map(_._2).sum} of ${per.map(_._3).sum}, and $probes probe(s) near them" +
        (if none.nonEmpty then s" (none for ${none.mkString(", ")}: unchecked, or its parameters are functions)" else "")

  /** The contracts whose code is the proven define, and proven to meet them. */
  def provenCode: List[Node[?]] =
    kb.nodes.filter(c => c.kind == NodeKind.Contract && generate.provenImpl(c).isDefined && kb.implementation(c).exists(_.provenCode) &&
      current(c).exists(k => k.status == "proven" && k.obligations.exists(o => o.name == "impl" && o.status == "proven")))

  /** Formal contracts whose translation no example cross-checks: checked, and none of their examples
    * evaluated in Lean as in Scala.
    */
  def uncrossed: List[String] =
    kb.nodes.filter(c => c.kind == NodeKind.Contract && generate.formal(c) && c.cases.nonEmpty).flatMap { c =>
      current(c).filter(k => !k.obligations.exists(o => o.name.startsWith("eval_") && o.status == "proven")).map(_ =>
        s"${c.id}: none of its examples is evaluated in Lean, so nothing checks that the Lean means what the Scala does: give its parameters values Lean has (bindTable for a lookup)")
    }

  /** Open requests from the developer (written by the browser). */
  def requests: List[Json] = allRequests.filter(_("status").flatMap(_.str).contains("open"))
  def allRequests: List[Json] = read(ws.requestsFile).map(Json.parse(_).arr.toList).getOrElse(Nil)

  /** Everything known about a node (docs/DAG.md §7): its idea section, the vocabulary it uses (terms,
    * meanings, definitions in force), the nodes above it with their reasons, the co-parts under each
    * parent, its parts, the alternatives rejected, what moved, and what the developer asked for. This is
    * what a fresh agent, or a new engineer, reads first.
    */
  def context(n: Node[?]): String =
    val g = generate
    val l = ledger
    val ann = annotated
    val st = ann("nodes").get.arr.map(x => x("id").flatMap(_.str).get -> x("state").flatMap(_.str).get).toMap
    val sb = StringBuilder()
    val section = (n :: kb.ancestors(n)).find(_.ideaSection.trim.nonEmpty)
    val ideaText = Decisions.ideaSections(ideaDecided)._1 + section.fold("")(s => "\n\n" + ideaOf(s)) +
      (if notModelledOfText(notModelled, section.getOrElse(n)).nonEmpty then s"\n\n## Not modelled\n\n${notModelledOfText(notModelled, section.getOrElse(n))}" else "")
    sb ++= s"# ${kb.name} / ${n.id}\n\n## Idea (${section.fold("its purpose")(s => s"the section ${s.ideaSection}")})\n\n${ideaText.trim}\n\n"
    def kind(x: Node[?]) = Workflow.kindName(x)
    // The decision that binds a node now, first; every accepted change to the node, newest first (each
    // marked if given for an earlier version of what it says); confirmations, briefly.
    def reasons(a: Node[?]): Unit =
      val ds = l.history(a.id).filter(d => Set("accept", "confirm", "revisit")(d.action))
      val nowHash = hash(a)
      def ver(d: Decision) = if d.hash == nowHash then "" else " [given for an earlier version of it]"
      def line(d: Decision) = d.action match
        case "accept" if l.chosen(a.id).contains(d) => s"Chosen by ${d.by} because: ${d.reason}${ver(d)}"
        case "accept"  => s"Change accepted by ${d.by}: ${d.reason}${ver(d)}"
        case "confirm" => s"Confirmed by ${d.by}: ${d.reason}"
        case _         => s"To revisit (${d.by}): ${d.reason}"
      ds.lastOption.foreach(d => sb ++= s"Latest: ${line(d)}\n\n")
      val accepts = ds.dropRight(1).filter(_.action == "accept").reverse
      // The latest few changes, and how it was chosen; the rest is in the ledger's history.
      val shown = (accepts.take(4) ++ accepts.filter(l.chosen(a.id).contains)).distinct
      shown.foreach(d => sb ++= s"${line(d)}\n\n")
      if accepts.size > shown.size then sb ++= s"(${accepts.size - shown.size} earlier accepted change(s) of ${a.id}: see its history in the browser)\n\n"
      val confirms = ds.dropRight(1).filter(_.action != "accept")
      if confirms.nonEmpty then sb ++= s"Earlier confirmations: ${confirms.takeRight(2).map(line).mkString(" / ")}${if confirms.size > 2 then s" (and ${confirms.size - 2} more)" else ""}\n\n"
      l.alternatives(a.id).foreach((id, c) => sb ++= s"- Rejected alternative $id: ${c("statement").flatMap(_.str).getOrElse("")} (why: ${c("why").flatMap(_.str).getOrElse("")})\n")
    def src(label: String, x: Lifted[?]) = sb ++= s"$label:\n```scala\n${x.source}\n```\n"
    def show(a: Node[?], depth: String) =
      sb ++= s"### ${a.id} (${kind(a)}) [${st.getOrElse(a.id, "?")}]$depth\n\n${a.statement}\n\nWhy: ${a.why}\n\n"
      reasons(a)
      a.formula.foreach(src("formula", _))
      a.post.foreach(src(s"post (of every call of ${a.op.fold("")(_.name)})", _))
      a.rule.foreach(src("rule", _))
      a.substs.foreach(s => sb ++= s"- `${s.name} := ${s.term.fold(s.lean)(_.source)}`\n")
      kb.limits(a).foreach(x => sb ++= s"- does not promise: $x\n")
      if kb.root.exists(_ eq a) then idleOf(a).foreach(w => sb ++= s"- doing nothing meets it ($w): it says only what must not happen; state what users can do\n")
      kb.exampleResults(a).foreach(r => sb ++= s"- example: ${r.example.describe} [${r.verdict}]\n")
      code(a).foreach(c => sb ++= s"- governs: ${c.files.mkString(", ")}\n")
      content(a)("implementation").flatMap(_.str).foreach(i => sb ++= s"implementation:\n```scala\n$i\n```\n")
      sb ++= "\n"
    // What its terms mean: the open terms, and the definitions in force (as decided).
    val used = kb.definitionsUsed(n, g.inForce)
    sb ++= "## Vocabulary it uses\n\n"
    vocabulary(n).foreach(v => sb ++= s"- $v\n")
    used.foreach(d => sb ++= s"- defined by ${d.id} [${st.getOrElse(d.id, "?")}]: ${d.statement} ${d.substs.map(s => s"`${s.name} := ${s.term.fold(s.lean)(_.source)}`").mkString(", ")}\n")
    val defs = Def.closure((n :: used).flatMap(_.referenced).flatMap(_.defs))
    defs.foreach(d => sb ++= s"```scala\n${d.name} = ${d.lifted.source}\n```\n")
    sb ++= "\n"
    // The nodes above, nearest first: each once, at its shortest distance.
    val above = kb.ancestors(n)
    if above.nonEmpty then
      sb ++= "## Above it (what it helps prove), nearest first\n\n"
      def dist(a: Node[?]): Int =
        def go(xs: List[Node[?]], d: Int, seen: Set[String]): Int =
          if xs.exists(_ eq a) then d else if xs.isEmpty then Int.MaxValue
          else go(xs.flatMap(kb.parentsOf).filterNot(x => seen(x.id)), d + 1, seen ++ xs.map(_.id))
        go(kb.parentsOf(n), 1, Set.empty)
      above.sortBy(dist).foreach(a => show(a, s" (${dist(a)} above)"))
    sb ++= "## The node\n\n"
    show(n, "")
    // Under each parent: the other parts, which together with this one make it, and those rejected there.
    kb.parentsOf(n).foreach { p =>
      val beside = kb.parts(p).filterNot(_ eq n)
      val rejected = l.rejectedUnder(p.id).filterNot((r, _, _) => r == n.id || beside.exists(_.id == r))
      if beside.nonEmpty || rejected.nonEmpty then
        sb ++= s"## Beside it, under ${p.id} (its co-parts: together they make ${p.id})\n\n"
        beside.foreach(o => sb ++= s"- ${o.id} (${kind(o)}) [${st.getOrElse(o.id, "?")}]: ${o.statement}\n")
        rejected.foreach((r, c, why) => sb ++= s"- rejected ${r}: ${c("statement").flatMap(_.str).getOrElse("")} — rejected because: $why\n")
        sb ++= "\n"
    }
    val parts = kb.children(n)
    if parts.nonEmpty then
      sb ++= s"## Its parts (a change here may affect them)\n\n"
      parts.foreach { c =>
        sb ++= s"- ${c.id} (${kind(c)}) [${st.getOrElse(c.id, "?")}]: ${c.statement} Why: ${c.why}\n"
        l.chosen(c.id).foreach(d => sb ++= s"  Chosen by ${d.by} because: ${d.reason}\n")
      }
      sb ++= "\n"
    // The contracts its code calls: proven from their promise alone.
    val calls = g.callees(n)
    if calls.nonEmpty then
      sb ++= "## Its code calls\n\n"
      calls.foreach { o =>
        sb ++= s"### ${o.id} (${kind(o)}) [${st.getOrElse(o.id, "?")}]\n\nIts code calls ${o.op.fold("")(_.name)}, and is proven from this promise alone (not from its code):\n\n${o.statement}\n\n"
        o.post.foreach(x => sb ++= s"```scala\n${x.source}\n```\n\n")
      }
    val users = kb.nodes.filter(c => !(c eq n) && restsOn(c).exists(_ eq n) && !kb.parentsOf(c).exists(_ eq n))
    if users.nonEmpty then
      sb ++= "## Rests on it besides its parts (a change to its meaning puts them up for review)\n\n"
      users.foreach(c => sb ++= s"- ${c.id} [${st.getOrElse(c.id, "?")}]: ${c.statement}\n")
      sb ++= "\n"
    // The cross-cutting rules that reach this node: every contract in their scope keeps them or is exempt.
    val invs = kb.nodes.filter(i => i.isInvariant && ((i eq n) || i.scope.isEmpty || (n :: kb.ancestors(n)).exists(a => i.scope.exists(_ eq a))))
    if invs.nonEmpty then
      sb ++= "## Invariants that apply here (every contract in their scope keeps them, or says why not)\n\n"
      invs.foreach { i =>
        sb ++= s"### ${i.id} [${st.getOrElse(i.id, "?")}]\n\n${i.statement}\n\nWhy: ${i.why}\n\n"
        i.rule.foreach(r => sb ++= s"rule:\n```scala\n${r.source}\n```\n")
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
          val (was, now) = (b.getOrElse(k, ""), a.getOrElse(k, ""))
          if !was.contains("\n") && !now.contains("\n") then s"  - $k\n    was: $was\n    now: $now\n"
          else s"  - $k (lines removed -, added +):\n" + Workflow.lineDiff(was, now).map("    " + _).mkString("\n") + "\n"
        }.mkString
      if causes.contains("self") then
        l.binding(n.id).foreach(d => sb ++= s"- ${n.id} itself changed:\n${fields(d.content, me("content").getOrElse(JNull))}")
      me("moved").map(_.arr.toList).getOrElse(Nil).foreach { m =>
        val a = m("id").flatMap(_.str).getOrElse("")
        val now = ann("nodes").get.arr.find(_("id").flatMap(_.str).contains(a)).flatMap(_("content")).getOrElse(JNull)
        sb ++= s"- the meaning of $a changed:\n${fields(m("before").getOrElse(JNull), now)}"
      }
      kb.parentsOf(n).filter(p => st.get(p.id).contains("rejected")).foreach(p => sb ++= s"- its parent ${p.id} was rejected: move it under the node chosen instead\n")
      if causes.contains("revisit") then
        l.current(n.id).filter(_.action == "revisit").foreach(r => sb ++= s"- ${r.by} asked to revisit it: ${r.reason}\n")
      if causes.contains("code") then
        val since = l.binding(n.id).map(d => if Git.has(ws.root, d.tree) then d.tree else d.commit).getOrElse("")
        val d = code(n).fold("")(c => Git.diff(ws.root, since, c.files))
        sb ++= (if d.nonEmpty then s"- the code it governs changed:\n```diff\n$d```\n" else "- the code it governs changed (no git diff available)\n")
        Decisions.codeNotes(ann, d).foreach(x => sb ++= s"- $x\n")
      sb ++= "\n"
    g.obligations(n).foreach { o =>
      val stl = current(n).flatMap(_.obligations.find(_.name == o.name)).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail.linesIterator.next()})" else ""}")
      sb ++= s"## Obligation ${o.name} of ${n.id} [$stl]\n\n${o.description}\n\n```lean\n${o.statement}\n```\n\n"
    }
    // What the last check left open or failed, with Lean's message in full (the goal it stopped at).
    current(n).orElse(checks.get(n.id)).foreach { c =>
      val bad = c.obligations.filter(!_.fine)
      if bad.nonEmpty || c.messages.nonEmpty then
        sb ++= s"## Last check of ${n.id}: ${c.status}${if current(n).isEmpty then " (before the latest change)" else ""}\n\n"
        bad.foreach(r => sb ++= s"- ${r.status} ${r.name}:\n```\n${r.detail}\n```\n")
        c.messages.foreach(m => sb ++= s"- $m\n")
        sb ++= "\n"
    }
    val asks = allRequests.filter(_("node").flatMap(_.str).contains(n.id))
    if asks.nonEmpty then
      sb ++= "## Requests from the developer\n\n"
      asks.foreach { r =>
        def f(k: String) = r(k).flatMap(_.str).getOrElse("")
        sb ++= s"- [${f("id")}, ${f("status")}] ${f("text")}${if f("answer").nonEmpty then s"\n  Answer: ${f("answer")}" else ""}\n"
      }
      sb ++= "\n"
    sb ++= s"A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.\nThe developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).\n"
    sb.result()

  // ---------------------------------------------------------------------------
  // Snapshot: what the browser and agents read
  // ---------------------------------------------------------------------------

  /** The knowledge base as data, from the Scala definitions and the checks; without decisions. */
  def baseSnapshot: Json =
    val g = generate
    def strs(xs: Seq[String]) = JArr(xs.map(str))
    val memo = scala.collection.mutable.Map.empty[String, String]
    def node(n: Node[?]): Json =
      val check = current(n)
      def res(name: String) = check.flatMap(_.obligations.find(_.name == name))
      val isRoot = kb.root.exists(_ eq n)
      obj(
        "id" -> str(n.id),
        "kind" -> str(Workflow.kindName(n)),
        "parents" -> strs(kb.parentsOf(n).map(_.id)),
        "parts" -> strs(kb.children(n).map(_.id)),
        "replaces" -> n.replaced.fold(JNull)(r => str(r.id)),
        "op" -> n.op.fold(JNull)(o => str(o.name)),
        "defines" -> strs(n.defines),
        "uses" -> strs(kb.definitionsUsed(n, g.inForce).map(_.id)),
        "rule" -> JBool(n.isInvariant),
        // Who decides it: its owner, else its first parent's; another knowledge base, if it is that one's.
        "owner" -> str(ownerOf(n)),
        "imported" -> kb.imports.get(n.id).fold(JNull)(i => str(i.kb)),
        "limits" -> strs(kb.limits(n)),
        // The root met by doing nothing: it says only what must not happen (see `Decisions.unproven`).
        "idle" -> Option.when(isRoot)(idleOf(n)).flatten.fold(JNull)(str),
        // The check of its statement: `proven`, `open`, `failed`, `waiting`, `unchecked`, `informal`; null for a definition or a design decision.
        "status" -> (if !kb.isStatement(n) then JNull else if !g.formal(n) then str("informal")
          else str(check.map(_.status).orElse(checks.get(n.id).filter(c => c.hash == checkHash(n)).map(_.status)).getOrElse("unchecked"))),
        // A claim nothing below proves: trusted as it stands (a hypothesis of root_impl).
        "leaf" -> JBool(n.kind == NodeKind.Claim && kb.parts(n).isEmpty),
        "examples" -> JArr(kb.exampleResults(n).zipWithIndex.map { (r, i) =>
          // What Lean computes of the example, against what Scala does (the examples written, not generated ones).
          def lean(name: String) =
            if i >= n.cases.size || !g.formal(n) then JNull
            else check.flatMap(_.obligations.find(_.name == name)).fold(obj("status" -> str("unchecked"), "detail" -> str("not checked yet")))(o =>
              obj("status" -> str(o.status), "detail" -> str(o.detail)))
          obj(
            "note" -> str(r.example.note), "given" -> strs(r.example.givens), "call" -> str(r.example.call),
            "expected" -> JBool(r.example.expected), "contract" -> str(r.contract),
            "implementation" -> r.implementation.fold(JNull)(str),
            "lean" -> lean(s"eval_$i"),
            "leanImplementation" -> (if g.provenImpl(n).isEmpty then JNull else lean(s"evalImpl_$i")))
        }),
        "code" -> code(n).fold(JNull)(c => obj(
          "files" -> strs(c.files), "fingerprint" -> str(c.fingerprint))),
        "content" -> content(n),
        "hash" -> str(hash(n)),
        "parentChain" -> str(restChain(n, memo)),
        "split" -> split(n),
        "invariants" -> JArr(n.kept.map { k =>
          val (st, detail) =
            if k.view.isEmpty then ("exempt", k.exempt)
            else if !g.formalKeeps(n).exists(_._1 eq k.invariant) then ("informal", "checked on the examples and at run time; not formalized")
            else
              // Kept: the view lists all the result holds of it, and the invariant's split holds with this contract needed.
              val inv = split(k.invariant)
              val cover = res(s"cover_${k.invariant.id}").map(r => (r.status, s"coverage: ${r.detail}"))
              val complete = inv("complete").map(c => (c("status").flatMap(_.str).getOrElse(""), c("detail").flatMap(_.str).getOrElse("")))
              val needed = inv("needed").flatMap(_.arr.find(_("id").flatMap(_.str).contains(n.id)))
                .map(c => (c("status").flatMap(_.str).getOrElse(""), c("detail").flatMap(_.str).getOrElse("")))
              val all = cover.toList ++ complete ++ needed
              all.find(_._1 != "proven").orElse(complete).getOrElse(("unchecked", "not checked yet"))
          obj("id" -> str(k.invariant.id), "view" -> str(k.view.fold("")(_.source)),
            "rule" -> str(k.invariant.rule.fold("")(_.source)), "status" -> str(st), "detail" -> str(detail))
        }),
        "expectations" -> JArr(n.expected.zipWithIndex.map { case ((st, l), i) =>
          val (status, detail) = if !g.formal(n) then ("informal", "not formalized")
            else res(s"expect_$i").fold(("unchecked", "not checked yet"))(r => (r.status, r.detail))
          obj("statement" -> str(st), "source" -> str(l.source), "status" -> str(status), "detail" -> str(detail))
        }),
        "implementationProof" -> kb.implementation(n).flatMap(_.proven).fold(JNull) { d =>
          val (st, detail) =
            if !g.formal(n) then ("informal", "the contract is out of Lean: checked on the examples and at run time")
            else res("impl").fold(("unchecked", "not checked yet"))(r => (r.status, r.detail))
          obj("name" -> str(d.name), "status" -> str(st), "detail" -> str(detail))
        },
        "rootImpl" -> (if !isRoot || !g.formal(n) then JNull
          else res("root_impl").fold(obj("status" -> str("unchecked"), "detail" -> str("not checked yet")))(r => obj("status" -> str(r.status), "detail" -> str(r.detail)))),
        "relies" -> strs(g.callees(n).map(_.id)),
        "covers" -> strs(if !n.isInvariant then Nil else kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty)).map(_.id)),
        "exempts" -> strs(if !n.isInvariant then Nil else kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty)).map(_.id)),
        "obligations" -> JArr(if !g.formal(n) then Nil else g.obligations(n).map(o => obj("name" -> str(o.name), "statement" -> str(o.statement), "description" -> str(o.description)))),
        "proof" -> read(ws.lean.resolve(g.proofsPath(n.id))).fold(JNull)(src => obj("file" -> str("lean/" + g.proofsPath(n.id)), "source" -> str(src))),
        "holds" -> str(if g.formal(n) then g.holdsStatement(n) else ""),
        "lean" -> str(if g.formal(n) then g.spec(n) else ""),
        "messages" -> strs(check.orElse(checks.get(n.id).filter(_.status == "waiting")).toList.flatMap(_.messages))
      )
    obj(
      "name" -> str(kb.name),
      "idea" -> str(idea),
      "format" -> JNum(Workflow.ContentFormat),
      "ideaFile" -> str(kb.idea),
      "warnings" -> strs(importWarnings ++ codeWarnings ++ uncrossed),
      "imports" -> JObj(importDirs.toList.sorted.map((id, d) => id -> str(d))),
      "root" -> kb.root.fold(JNull)(r => str(r.id)),
      "definitions" -> strs(kb.definitions.map(_.id)),
      "trusted" -> strs(if kb.root.exists(g.formal) then g.trusted.map(_.id) else Nil),
      "exportedAt" -> str(java.time.Instant.now.toString),
      "opaques" -> JArr(kb.opaques.map(o => obj("name" -> str(o.name), "means" -> str(o.means), "definedBy" -> g.inForce.get(o.name).fold(JNull)(d => str(d.id))))),
      "params" -> JArr(kb.params.map(p => obj(
        "name" -> str(p.name), "means" -> str(p.means), "operation" -> JBool(kb.isOp(p.name)),
        "definedBy" -> g.inForce.get(p.name).fold(JNull)(d => str(d.id)),
        "type" -> str(kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).toMap.getOrElse(p.name, ""))))),
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
  /** The right side of a `val` that is a value, not code: literals, and constructors applied to values
    * (`= Account("ann@acme", TenantId("acme"))`, `= List(…)`), with no lambda, block or method call.
    */
  def isData(rest: String): Boolean =
    val r = rest.trim.stripPrefix(":").trim
    val rhs = r.drop(r.indexOf('=') + 1).trim
    r.contains("=") && rhs.nonEmpty && !rhs.contains("=>") && !rhs.contains("{") &&
      """\.[a-z]\w*""".r.findFirstIn(rhs.replaceAll("\"[^\"]*\"", "\"\"").replaceAll("""\d+\.\d+""", "0")).isEmpty &&
      """^[A-Z"0-9(\-]""".r.findFirstIn(rhs).isDefined
  /** A method in a Scala file: its name, whether it returns Unit (it changes something), its lines, and its body. */
  final case class Method(name: String, unit: Boolean, lines: Int, body: String, priv: Boolean)

  /** The methods of a file, by indentation: a `def` and the lines indented under it. */
  def methods(text: String): List[Method] =
    val ls = text.linesIterator.toVector
    val Def = """^(\s*)((?:private(?:\[\w+\])?|protected|override|final|inline)\s+)*def\s+(\w+)(.*)$""".r
    def indent(l: String) = l.takeWhile(_ == ' ').length
    ls.indices.toList.flatMap(i => ls(i) match
      case Def(sp, mods, name, rest) =>
        val end = ls.indices.drop(i + 1).find(j => ls(j).trim.nonEmpty && indent(ls(j)) <= sp.length).getOrElse(ls.size)
        val body = ls.slice(i, end).filter(_.trim.nonEmpty)
        val header = (rest + " " + ls.slice(i + 1, end).takeWhile(!_.contains("=")).mkString(" ")).takeWhile(_ != '=')
        Some(Method(name, """\)\s*:\s*Unit\s*$""".r.findFirstIn(header.trim).isDefined || header.trim.endsWith(": Unit"),
          body.size, body.mkString("\n"), Option(mods).exists(_.contains("private"))))
      case _ => None)

  /** The lines of the named methods of a file, with the private methods they call, however deep. */
  def linesOf(text: String, names: Set[String]): Int =
    val ms = methods(text)
    val byName = ms.groupBy(_.name)
    def close(seen: Set[String]): Set[String] =
      val more = seen.flatMap(n => byName.getOrElse(n, Nil)).flatMap(m => ms.filter(p => p.priv && !seen(p.name) && s"\\b${p.name}\\b".r.findFirstIn(m.body).isDefined).map(_.name))
      if more.isEmpty then seen else close(seen ++ more)
    close(names.filter(byName.contains)).toList.flatMap(byName).map(_.lines).sum

  /** The first line of a proof copied from another knowledge base. */
  val CopiedProof = "-- Copied by FrFlow from"
  /** A ledger with the decisions of the nodes other knowledge bases decide (id -> their project's directory). */
  def withImports(own: Ledger, imports: Map[String, String]): Ledger =
    imports.groupBy(_._2).foldLeft(own) { case (l, (root, ids)) =>
      val theirs = Ledger.load(Path.of(root).resolve(".frflow/ledger.json"))
      Ledger(l.decisions ++ theirs.decisions.filter((id, _) => ids.contains(id)))
    }
  /** A node's kind as the snapshot names it. */
  def kindName(n: Node[?]): String = n.kind.toString.toLowerCase
  /** The lines removed (`- `) and added (`+ `) from `a` to `b`, in order (a longest common subsequence). */
  def lineDiff(a: String, b: String): List[String] =
    val (x, y) = (a.split("\n", -1).toVector, b.split("\n", -1).toVector)
    val lcs = Array.ofDim[Int](x.size + 1, y.size + 1)
    for i <- x.indices.reverse; j <- y.indices.reverse do
      lcs(i)(j) = if x(i) == y(j) then lcs(i + 1)(j + 1) + 1 else lcs(i + 1)(j).max(lcs(i)(j + 1))
    val out = List.newBuilder[String]
    var (i, j) = (0, 0)
    while i < x.size || j < y.size do
      if i < x.size && j < y.size && x(i) == y(j) then { i += 1; j += 1 }
      else if j < y.size && (i == x.size || lcs(i)(j + 1) >= lcs(i + 1)(j)) then { out += s"+ ${y(j)}"; j += 1 }
      else { out += s"- ${x(i)}"; i += 1 }
    out.result()

  /** The shape of a node's content, which decisions are bound to. A snapshot of another shape is
    * not decided on: it was written by another version of FrFlow, and must be rendered again.
    */
  val ContentFormat: Int = 4

  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 4
