package frflow
package check

import frflow.lean.*
import frflow.ledger.*
import frflow.protocol.{NodeKind as Kind, *}
import io.circe.Json
import io.circe.syntax.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
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
  private def id(n: Node[?]): NodeId = NodeId(n.id)
  private def ids(ns: Seq[Node[?]]): List[NodeId] = ns.map(id).toList
  private def str(s: String): Json = Json.fromString(s)
  private def strs(xs: Seq[String]): Json = Json.fromValues(xs.map(Json.fromString))

  def idea: String = read(ws.root.resolve(kb.idea)).getOrElse("")
  def ledger: Ledger = LedgerStore.load(ws.ledgerFile)
  private var checksCache: Option[(String, Map[NodeId, NodeCheck])] = None
  /** The recorded checks (read again when the file changes). */
  def checks: Map[NodeId, NodeCheck] = synchronized {
    val f = ws.checksFile
    val stamp = if Files.exists(f) then s"${Files.size(f)}:${Files.getLastModifiedTime(f).toMillis}" else ""
    checksCache.filter(_._1 == stamp).map(_._2).getOrElse { val c = Checks.load(f); checksCache = Some(stamp -> c); c }
  }

  /** The obligations proven by a theorem of their name in the node's proof file: (node, obligation). */
  def proofs: Set[(String, ObligationName)] =
    val base = baseGenerate
    kb.nodes.flatMap { n =>
      val names = base.obligations(n).map(_.name).toSet + ObligationName.Feasible
      read(ws.lean.resolve(base.layout.proofs(n.id).path)).toList.flatMap(src =>
        Lean.theorems(src).flatMap(t => ObligationName.parse(t.name)).filter(names).map(n.id -> _))
    }.toSet

  /** Nodes whose `complete` has an authored proof. */
  def authored(id: String): Boolean = proofs((id, ObligationName.Complete))

  /** The definitions the developer chose (accepted, and not since rejected): among two definitions of a
    * term, the one in force.
    */
  def chosen(id: String): Boolean =
    ledger.binding(NodeId(id)).isDefined && !ledger.current(NodeId(id)).exists(_.action == Action.Reject)

  private lazy val baseGenerate = Generate(kb)

  /** The proof files as they are now (names, sizes, times), and the definitions chosen among
    * alternatives: what `generate` and check hashes are cached by.
    */
  private def proofStamp: String =
    val dir = ws.lean.resolve(baseGenerate.layout.proofs("x").path).getParent
    val files = if !Files.isDirectory(dir) then ""
      else scala.util.Using.resource(Files.list(dir))(_.iterator.asScala.toList).sorted
        .map(f => s"${f.getFileName}:${Files.size(f)}:${Files.getLastModifiedTime(f).toMillis}").mkString(",")
    files + "|" + kb.definitionsOf.values.filter(_.size > 1).flatten.map(_.id).filter(chosen).toList.sorted.mkString(",")
  private var cached: Option[(String, Generate, scala.collection.concurrent.TrieMap[String, Hash])] = None
  private def cache: (Generate, scala.collection.concurrent.TrieMap[String, Hash]) = synchronized {
    val stamp = proofStamp
    cached.filter(_._1 == stamp).fold { val c = (stamp, Generate(kb, proofs, chosen), scala.collection.concurrent.TrieMap.empty[String, Hash]); cached = Some(c); (c._2, c._3) }(c => (c._2, c._3))
  }
  def generate: Generate = cache._1

  /** Writes the generated Lean; returns the files that changed. */
  def render(): List[String] =
    val g = generate
    write(ws.lean.resolve("lakefile.toml"), g.lakefile(ws.kernelPath))
    write(ws.lean.resolve("lean-toolchain"), "leanprover/lean4:v4.35.0\n")
    val files = g.files
    val changed = files.toList.sortBy(_._1).collect { case (rel, text) if write(ws.lean.resolve(rel), text) => rel }
    val keep = files.keySet.map(ws.lean.resolve(_).normalize)
    g.layout.generatedDirs.map(ws.lean.resolve).filter(Files.isDirectory(_)).foreach { d =>
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

  /** The terms a node mentions, with what they mean in the world. */
  def vocabulary(n: Node[?]): List[String] =
    val terms = kb.termsOf(n).toSet ++ n.defines
    (kb.opaques.filter(o => terms(o.name)).map(o => s"${o.name}: ${o.means}") ++ kb.params.filter(p => terms(p.name)).map(p => s"${p.name}: ${p.means}")).sorted

  /** The node as the developer sees it and decides it. A decision is bound to its hash. A statement's
    * parts are part of it (docs/DAG.md §5): a part added or removed reviews it, with the cause `parts`.
    */
  def content(n: Node[?]): Content = Content((Seq(
    "kind" -> str(Workflow.kindOf(n).toString),
    "parents" -> strs(n.parents.map(_.id))) ++
    Option.when(kb.isStatement(n))("parts" -> strs(kb.parts(n).map(_.id))) ++ Seq(
    "statement" -> str(n.statement),
    "why" -> str(n.why),
    "sources" -> Json.obj(Seq("formula" -> n.formula, "post" -> n.post, "rule" -> n.rule, "check" -> n.local).collect { case (k, Some(l)) => k -> str(l.source) }*),
    "substitutions" -> strs(n.substs.map(s => s"${s.name} := ${s.term.fold(s.lean)(_.source)}")),
    "examples" -> strs(n.cases.map(_.describe)),
    "vocabulary" -> strs(vocabulary(n)),
    "uses" -> strs(generate.sourcesUsedBy(n)),
    "governs" -> strs(n.governs),
    "definition" -> str(definition(n))
  ) ++ n.op.map(o => "op" -> str(o.name)) ++ n.replaced.map(r => "replaces" -> str(r.id)) ++
    (if n.formal then Nil else List("formal" -> Json.False)) ++
    (if n.kept.isEmpty then Nil else List("keeps" -> strs(n.kept.map(_.describe)))) ++
    (if n.expected.isEmpty then Nil else List("expects" -> strs(n.expected.map((st, l) => s"$st: ${l.source}")))) ++
    kb.implementation(n).flatMap { i =>
      val proven = i.proven.toList.flatMap(d => s"proven: ${d.name}" +: Def.closure(List(d)).map(x => s"${x.name} = ${x.lifted.source}"))
      val runs = Option.when(i.wiring.nonEmpty)(if i.proven.isDefined then s"runs: ${i.wiring}" else i.wiring).toList
      Option.when((proven ++ runs).nonEmpty)("implementation" -> str((proven ++ runs).mkString("\n")))
    }.toList
    ++ {
      // The root is decided against the idea's title and lead; a node naming a section, against that section.
      if n.ideaSection.nonEmpty then Seq("idea" -> str(ideaOf(n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(notModelled))
      else if kb.root.exists(_ eq n) then Seq("idea" -> str(Decisions.ideaSections(ideaDecided)._1), "notModelled" -> str(notModelled))
      else Nil
    })*)

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
  def ideaOf(n: Node[?]): String =
    Decisions.ideaSections(ideaDecided)._2.find(_._1.equalsIgnoreCase(n.ideaSection.trim)).map(_._2).getOrElse("")

  /** Sections of the idea no node is decided against, and nodes naming a section the idea does not have. */
  def ideaCoverage: List[String] =
    val named = kb.nodes.map(_.ideaSection.trim).filter(_.nonEmpty)
    val sections = Decisions.ideaSections(ideaDecided)._2.map(_._1)
    sections.filterNot(h => named.exists(_.equalsIgnoreCase(h)))
      .map(h => s"the section \"$h\" of ${kb.idea} is the concern of no node: name it on the node that states it (idea = \"$h\"), or move it to Not modelled") ++
      kb.nodes.filter(_.ideaSection.trim.nonEmpty).filterNot(n => sections.exists(_.equalsIgnoreCase(n.ideaSection.trim)))
        .map(n => s"${n.id} is decided against the section \"${n.ideaSection}\", which ${kb.idea} does not have")

  def hash(n: Node[?]): Hash = content(n).hash

  /** The nodes a node rests on: its parents, the definitions it uses, and the contracts its code calls
    * (the snapshot's `parents`, `uses` and `relies`, from which the ledger computes each node's chain).
    */
  def restsOn(n: Node[?]): List[Node[?]] =
    (kb.parentsOf(n) ++ kb.definitionsUsed(n, generate.inForce) ++ generate.callees(n)).distinctBy(_.id)

  /** Files governed explicitly by some node. */
  private lazy val governedExplicitly: Set[Path] =
    kb.nodes.flatMap(_.governs).map(f => ws.root.resolve(f).toAbsolutePath.normalize).toSet

  /** What a check depends on: the formal parts only, so rewording a statement does not re-run Lean. It
    * covers the node's Lean, its proof file, the definitions it uses, its parts' and its callees' checks
    * (and, for the root, everything `root_impl` is composed of).
    */
  def checkHash(n: Node[?]): Hash =
    val (g, hashes) = cache
    def go(n: Node[?], seen: Set[String]): Hash = hashes.getOrElse(n.id, {
      val proof = read(ws.lean.resolve(g.layout.proofs(n.id).path))
      val h = Hash(sha((Seq(g.spec(n), g.auto(n), g.theorems(n), g.checks(n), g.evalFile(n).getOrElse(""), g.provenImpl(n).fold("")(_ => g.impl(n)),
        if kb.root.exists(_ eq n) then g.rootImpl.fold("")(_._2) else "",
        proof.getOrElse(""), proof.filter(Lean.lemmaImports(_).nonEmpty).flatMap(_ => read(ws.lean.resolve(g.layout.lemmas.path))).getOrElse(""),
        // The specs of other nodes a proof imports: a change to them re-checks it.
        proof.fold("")(src => s"(?m)^\\s*import\\s+FrFlowGen\\.${java.util.regex.Pattern.quote(kb.name)}\\.(\\w+)\\.Spec".r
          .findAllMatchIn(src).map(_.group(1)).filter(_ != n.id).flatMap(kb.node).filter(g.formal).map(g.spec).mkString),
        // A node's proofs read its parts' and callees' statements (and its `holds`, its parts' `holds`,
        // over the leaves below them), not how those are proven or coded: a change of code below
        // re-checks only the contract and the root's `root_impl`, not every ancestor.
        (kb.parts(n) ++ g.callees(n)).filter(g.formal).distinctBy(_.id).filterNot(c => c eq n).map(g.spec).mkString,
        kb.parts(n).filter(g.formal).filterNot(c => c eq n).map(g.holdsStatement).mkString,
        // `root_impl` composes every proof and every implementation: the root depends on all of them.
        (if kb.root.exists(_ eq n) then (g.trusted ++ kb.nodes.filter(c => g.provenImpl(c).isDefined) ++ kb.nodes.filter(g.formal))
          .distinctBy(_.id).filterNot(c => seen(c.id) || (c eq n)).map(go(_, seen + n.id).value).mkString else ""),
        Workflow.CheckerVersion.toString) ++ g.declarationsUsedBy(n))*))
      hashes(n.id) = h
      h
    })
    go(n, Set.empty)

  // ---------------------------------------------------------------------------
  // Check
  // ---------------------------------------------------------------------------

  /** Checks nodes (all, or one), parts first, and records the results. */
  def check(only: Option[String] = None): List[(Node[?], NodeCheck)] =
    render()
    val lake = Lake(ws.lean)
    val g = generate
    val todo = kb.ordered.filter(g.formal).filter(n => only.forall(_ == n.id))
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
    // A node whose formal parts did not change keeps its result.
    def unchanged(n: Node[?]) = current(n).filter(_ => only.isEmpty)
    val pending = todo.filter(unchanged(_).isEmpty)
    // The models first, in one build Lake runs in parallel. A batch that builds is built for each of
    // its targets: their own builds are skipped (one at a time, they cost about as much as Lean's start).
    val built = java.util.concurrent.ConcurrentHashMap.newKeySet[String]()
    def batch(targets: Seq[String]): Unit =
      if targets.size > 1 && lake.buildAll(targets).ok then targets.foreach(built.add)
    // The proofs of the code too (each imports only models): one at a time, they were most of a cold
    // check. Each node's own build of it then replays it, with its messages (the axioms it rests on).
    val ready = pending.filter(g.waitsForDefinition(_).isEmpty)
    batch(ready.map(n => g.layout.spec(n.id).name) ++ ready.filter(g.obligation(_, ObligationName.Impl).isDefined).map(n => g.layout.impl(n.id).name))
    val threads = sys.env.get("FRFLOW_THREADS").flatMap(_.toIntOption).getOrElse(Runtime.getRuntime.availableProcessors.min(4)).max(1)
    val pool = java.util.concurrent.Executors.newFixedThreadPool(threads)
    val done = scala.collection.concurrent.TrieMap.empty[String, NodeCheck]
    try todo.groupBy(level(_, Set.empty)).toList.sortBy(_._1).foreach { (_, ns) =>
      // A level's theorems in one build, which Lake runs in parallel (builds are one at a time).
      batch(ns.filter(n => unchanged(n).isEmpty && g.waitsForDefinition(n).isEmpty).map(n => g.layout.theorems(n.id).name))
      ns.map { n =>
        val partStatus = kb.parts(n).filter(g.formal).map(p => p.id -> done.get(p.id).orElse(current(p)).map(_.status))
        // A node is proven with its parts: kept as it was only while they all are.
        val kept = unchanged(n).filter(_ => partStatus.forall(_._2.contains(CheckStatus.Proven)))
        n -> pool.submit(() => kept.getOrElse(checkNode(n, g, lake, partStatus, built.contains)))
      }.foreach((n, f) => done(n.id) = f.get())
    }
    finally pool.shutdown()
    val results = todo.map(n => n -> done(n.id))
    val kept = checks.filter((id, _) => kb.node(id.value).isDefined)
    val all = results.foldLeft(kept)((m, r) => m.updated(id(r._1), r._2))
    Checks.save(ws.checksFile, all)
    synchronized { checksCache = None }
    results

  private def checkNode(n: Node[?], g: Generate, lake: Lake, partStatus: List[(String, Option[CheckStatus])], built: String => Boolean = _ => false): NodeCheck =
    def build(target: String) = if built(target) then Run(0, "") else lake.build(target)
    // The examples, evaluated in Lean: every result carries them.
    var evaluated: List[Result] = Nil
    def done(status: CheckStatus, rs: List[Result], msgs: List[String], axioms: List[String] = Nil) =
      NodeCheck(checkHash(n), status, rs ++ evaluated, msgs, axioms, java.time.Instant.now.toString)
    def errors(r: Run) =
      val ds = Lean.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
      if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))
    def timedOut(r: Run) = !r.ok && r.output.contains("timed out after")

    // Two definitions of a term it uses, neither chosen: what it says is not known yet.
    val waits = g.waitsForDefinition(n)
    if waits.nonEmpty then return done(CheckStatus.Waiting, Nil, List(s"waits for the choice between the definitions of ${waits.mkString(", ")} (${waits.flatMap(t => kb.definitionsOf(t).map(_.id)).mkString(", ")})"))

    val spec = build(g.layout.spec(n.id).name)
    // A timeout is not a broken model: the machine was busy, or Lean slow; it is checked again.
    if timedOut(spec) then return done(CheckStatus.Timeout, Nil, List("Lean timed out building the model (the machine may be busy): run check again"))
    if !spec.ok then return done(CheckStatus.ModelError, Nil, errors(spec))

    // Lemmas shared by the proof files: the same filter, built.
    val proofSrc = read(ws.lean.resolve(g.layout.proofs(n.id).path)).getOrElse("")
    val lemmas = Lean.lemmaImports(proofSrc)
    if lemmas.nonEmpty then
      if lemmas != List(g.layout.lemmas.name) then return done(CheckStatus.Failed, Nil, List(s"a proof file may import only ${g.layout.lemmas.name}, not ${lemmas.mkString(", ")}"))
      val lsrc = read(ws.lean.resolve(g.layout.lemmas.path))
      if lsrc.isEmpty then return done(CheckStatus.Failed, Nil, List(s"the proof imports ${g.layout.lemmas.name}, but lean/${g.layout.lemmas.path} does not exist"))
      val bad = lsrc.flatMap(Lean.notAllowedInLemmas)
      if bad.nonEmpty then return done(CheckStatus.Failed, Nil, List(s"not allowed in lean/${g.layout.lemmas.path}: ${bad.mkString}"))
      val built = lake.build(g.layout.lemmas.name)
      if !built.ok then return done(CheckStatus.Failed, Nil, "the lemmas do not build" :: errors(built))
      if Lean.usesSorry(built.output) then return done(CheckStatus.Failed, Nil, List(s"lean/${g.layout.lemmas.path} uses sorry"))

    // Scala and Lean must agree on every example: what Scala computes of it, Lean proves; its
    // opposite, Lean does not. A disagreement means the translation does not mean what the Scala does,
    // and nothing proven of the node is about the code.
    val (evals, notEvaluated) = g.evals(n)
    if evals.nonEmpty then
      val rel = g.layout.eval(n.id).path
      val run = lake.elaborate(rel)
      val lean = Elaboration(read(ws.lean.resolve(rel)).getOrElse(""), run.output, rel)
      evaluated = evals.map { e =>
        val name = e.name.lean
        (lean.proves(name), lean.proves(name + "_opposite")) match
          case _ if lean.diagnostics.isEmpty && !run.ok => Result(name, ObligationStatus.Unevaluated, s"${e.what}: Lean did not run: ${run.output.take(20000)}")
          case (true, false) => Result(name, ObligationStatus.Proven, s"Lean agrees: ${e.claim}")
          case (false, true) => Result(name, ObligationStatus.Failed, s"${e.what}: Scala computes ${e.claim}, Lean proves ${e.opposite}")
          case (true, true)  => Result(name, ObligationStatus.Failed, s"${e.what}: Lean proves both ${e.claim} and its opposite")
          case (false, false) => Result(name, ObligationStatus.Unevaluated, s"${e.what}: Lean decides neither ${e.claim} nor its opposite")
      }.filterNot(r => ObligationName.parse(r.name).exists(_.isProbe) && r.status == ObligationStatus.Unevaluated) // a probe Lean cannot decide says nothing
    evaluated ++= notEvaluated.map((name, why) => Result(name.lean, ObligationStatus.Unevaluated, why))
    val disagree = evaluated.filter(_.status == ObligationStatus.Failed)
    if disagree.nonEmpty then return done(CheckStatus.Failed, Nil,
      s"Lean and Scala disagree on ${disagree.size} example(s) or probe(s): the Lean translation does not mean what the Scala does, so nothing proven of ${n.id} is about the code" :: disagree.map(_.detail))

    // A theorem of a file: proven when Lean reports no error in it and no `sorry`; an authored one must
    // state exactly its obligation and use only what a proof file may.
    def judge(o: ObligationName, rel: String, run: Run, isAuthored: Boolean): Result =
      val name = o.lean
      val lean = Elaboration(read(ws.lean.resolve(rel)).getOrElse(""), run.output, rel)
      val bad = if isAuthored then Lean.notAllowed(lean.source) else None
      lean.theorem(name) match
        case None => Result(name, ObligationStatus.Open, s"no theorem $name in $rel")
        case Some(d) if d.statement != s"Obl.$name" => Result(name, ObligationStatus.Failed, s"must state exactly Obl.$name")
        case Some(_) if bad.nonEmpty => Result(name, ObligationStatus.Failed, s"not allowed in a proof file: ${bad.mkString}")
        case Some(_) => lean.verdict(name) match
          case TheoremVerdict.Proven if run.ok => Result(name, ObligationStatus.Proven, if isAuthored then "authored" else "auto")
          case TheoremVerdict.Proven => Result(name, ObligationStatus.Open, "not checked: " + run.output.take(20000))
          case v => Result(name, ObligationStatus.Open, v.why(name).getOrElse("").take(20000))

    // Its parts make it: built already (with its level), automatic `complete` is proven without elaborating it again.
    val split = g.obligation(n, ObligationName.Complete).toList.map { o =>
      val prebuilt = Option.when(!authored(n.id))(build(g.layout.theorems(n.id).name)).filter(_.ok)
      if prebuilt.isDefined then Result(o.name.lean, ObligationStatus.Proven, "auto")
      else
        val rel = if authored(n.id) then g.layout.proofs(n.id).path else g.layout.auto(n.id).path
        val r = judge(o.name, rel, lake.elaborate(rel), authored(n.id))
        // Automation is tried only while no proof file proves it: what to do next comes first.
        if authored(n.id) || r.status != ObligationStatus.Open then r
        else r.copy(detail = s"automation gave up: write theorem complete : Obl.complete in lean/${g.layout.proofs(n.id).path} (run `scaffold ${n.id}`)\n" +
          proofState(n, ObligationName.Complete, g, lake).fold(s"Lean: ${r.detail}")(stateText(ObligationName.Complete, _)))
    }
    // Its code meets it, from what the contracts it calls promise.
    var implAxioms: List[String] = Nil
    val implemented = g.obligation(n, ObligationName.Impl).toList.map { o =>
      val auth = g.isAuthored(n, ObligationName.Impl)
      if auth then
        val bad = Lean.notAllowed(proofSrc)
        val stated = Lean.theorems(proofSrc).find(_.name == "impl").map(_.statement)
        if bad.nonEmpty then Result("impl", ObligationStatus.Failed, s"not allowed in a proof file: ${bad.mkString}")
        else if !stated.contains("Obl.impl") then Result("impl", ObligationStatus.Failed, "must state exactly Obl.impl")
        else
          val run = lake.build(g.layout.impl(n.id).name)
          implAxioms = Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List("<no audit result>"))
          if run.ok && !implAxioms.contains("sorryAx") then Result("impl", ObligationStatus.Proven, "authored")
          else if run.ok then Result("impl", ObligationStatus.Open, "uses sorry")
          else Result("impl", ObligationStatus.Open, s"not proven (authored): " + errors(run).take(3).mkString("\n").take(20000))
      else
        val run = lake.build(g.layout.impl(n.id).name)
        implAxioms = Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List("<no audit result>"))
        if run.ok then Result("impl", ObligationStatus.Proven, "auto")
        else Result("impl", ObligationStatus.Open, s"not proven (auto): prove theorem impl : Obl.impl in lean/${g.layout.proofs(n.id).path} (run `scaffold ${n.id}`)\n" +
          proofState(n, ObligationName.Impl, g, lake).fold("Lean: " + errors(run).take(3).mkString("\n").take(20000))(stateText(ObligationName.Impl, _)))
    }
    val results = split ++ implemented
    if results.exists(_.status == ObligationStatus.Failed) then return done(CheckStatus.Failed, results, Nil)
    if split.exists(_.status == ObligationStatus.Open) then
      return done(CheckStatus.Open, results, List(s"prove it in lean/${g.layout.proofs(n.id).path} (run `scaffold ${n.id}`)"))
    val notYet = partStatus.filterNot(_._2.contains(CheckStatus.Proven))
    if notYet.nonEmpty then return done(CheckStatus.Waiting, results, List(s"waiting for its parts: ${notYet.map(_._1).mkString(", ")}"))

    val thms = build(g.layout.theorems(n.id).name)
    if timedOut(thms) then return done(CheckStatus.Timeout, results, List("Lean timed out building the node's theorems: run check again"))
    if !thms.ok then return done(CheckStatus.Failed, results, "the node's theorems do not build" :: errors(thms))
    // The proof file, when it proves obligations of the Checks file.
    val proofFile: Option[String] =
      if !g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) then None
      else
        val bad = Lean.notAllowed(proofSrc)
        if bad.nonEmpty then Some(s"not allowed in lean/${g.layout.proofs(n.id).path}: ${bad.mkString}")
        else
          val built = lake.build(g.layout.proofs(n.id).name)
          Option.when(!built.ok)(s"lean/${g.layout.proofs(n.id).path} does not build: " + errors(built).take(5).map(_.take(20000)).mkString("\n"))
    // Everything else imports it: what it proves fails, by name, and the file is the message.
    if proofFile.isDefined then return done(CheckStatus.Failed,
      results ++ g.extraObligations(n).filter(o => g.isAuthored(n, o.name)).map(o => Result(o.name.lean, ObligationStatus.Failed, proofFile.get)), List(proofFile.get))
    // Everything else, in one run of Lean (see `Generate.checks`): each theorem holds when Lean reports
    // no error in it, no `sorry`, and its axioms (fail closed: no audit, no proof).
    def elaborated(rel: String): (Run, String => Option[String], String => Option[List[String]]) =
      val run = lake.elaborate(rel)
      val lean = Elaboration(read(ws.lean.resolve(rel)).getOrElse(""), run.output, rel)
      (run, name => lean.verdict(name).why(name).map(_.take(20000)), lean.axiomsOf)
    val rel = g.layout.checks(n.id).path
    val (run, why, axiomsOf) = elaborated(rel)
    if timedOut(run) then return done(CheckStatus.Timeout, results, List("Lean timed out checking the node (the machine may be busy): run check again"))
    def holds(name: String) = why(name).isEmpty
    // The tries: what Lean proves of them says the node or its split says nothing, or too much.
    val tried = g.tries(n).map(t => (t, holds(t.obligation.name.lean)))
    val fatal = tried.collect { case (t, true) if t.kind.fatal => t.means }
    // Each in plain words: what Lean proved, or that it found no proof within the try's budget (see `TryKind`).
    lazy val idle = g.idleWhat(n)
    val one = g.splitParts(n).collect { case List(c) => c.id }.getOrElse("")
    val tryResults = tried.map { (t, proven) =>
      Result(t.obligation.name.lean, if proven then t.kind.onProven else t.kind.onNot,
        if !proven then t.kind.unshown(n.id, one, idle) else if t.kind == TryKind.Idle then idle else t.means)
    }
    val extra = g.extraObligations(n).map { o =>
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      val name = o.name.lean
      val vacuous = o.name match
        case ObligationName.Expect(i) => tried.exists((t, p) => p && t.kind == TryKind.VacuousExpect(i))
        case _                        => false
      if vacuous then (Result(name, ObligationStatus.Failed, "it holds whatever the node says: it checks nothing"), Nil)
      else why(name) match
        case None => (Result(name, ObligationStatus.Proven, how), axiomsOf(name).getOrElse(List("<no audit result>")))
        case Some("uses sorry") => (Result(name, ObligationStatus.Open, "uses sorry"), Nil)
        case Some(w) => (Result(name, ObligationStatus.Open, s"not proven ($how): prove theorem $name : Obl.$name in lean/${g.layout.proofs(n.id).path}\nLean: $w"), Nil)
    }
    // A view whose coverage cannot be stated keeps nothing proven.
    val uncovered = g.formalKeeps(n).flatMap((i, _) => g.coverage(n, i).left.toOption.map(w =>
      Result(ObligationName.Cover(i.id).lean, ObligationStatus.Failed, s"what the view must list cannot be stated: $w")))
    // The root, of the code: from what is trusted only.
    val (rootImpl, rootAxioms) = g.rootImpl.filter(_ => kb.root.exists(_ eq n)).fold((List.empty[Result], List.empty[String])) { _ =>
      val (rrun, rwhy, raxioms) = elaborated(g.layout.rootImpl.path)
      rwhy("root_impl") match
        case None => (List(Result("root_impl", ObligationStatus.Proven, s"the root holds of the code, trusting ${if g.trusted.isEmpty then "nothing" else g.trusted.map(_.id).mkString(", ")}")),
          raxioms("root_impl").getOrElse(List("<no audit result>")))
        case Some(w) => (List(Result("root_impl", ObligationStatus.Open, s"the root is not proven of the code: $w${if rrun.ok then "" else "\n" + errors(rrun).take(3).mkString("\n").take(5000)}")), Nil)
    }
    val used = (axiomsOf("holds").getOrElse(List("<no audit result>")) ++ extra.flatMap(_._2) ++ (if implemented.exists(_.status == ObligationStatus.Proven) then implAxioms else Nil) ++
      rootAxioms).distinct.sorted
    val all = results ++ extra.map(_._1) ++ uncovered ++ tryResults ++ rootImpl
    if fatal.nonEmpty then done(CheckStatus.Failed, all, fatal, used)
    else if used.contains("<no audit result>") then
      done(CheckStatus.Failed, all, List(s"Lean did not finish checking lean/$rel: " + errors(run).take(3).map(_.take(5000)).mkString("\n")), used)
    else if used.exists(a => !Lean.allowedAxioms(a)) then done(CheckStatus.Failed, all, List(s"disallowed axioms: ${used.filterNot(Lean.allowedAxioms).mkString(", ")}"), used)
    // (What is left open is in the results, once: not repeated as messages.)
    else done(CheckStatus.Proven, all, Nil, used)

  /** The recorded check of a node, if still current. */
  def current(n: Node[?]): Option[NodeCheck] =
    // A result that waited, or timed out, is not final: it is checked again.
    if !generate.formal(n) then None
    else checks.get(id(n)).filter(c => c.hash == checkHash(n) && !Set(CheckStatus.Waiting, CheckStatus.Timeout, CheckStatus.ModelError)(c.status))

  /** The source files a node governs: a contract's implementation, a design decision's files. */
  def code(n: Node[?]): Option[CodeRef] =
    // An implementation governs the files of the code its expression refers to (not the model's
    // file); anything else it depends on is governed explicitly (a design node owning a
    // directory), or `status` reports it as governed by no node.
    val impl = kb.implementation(n).toList.flatMap { i =>
      i.sources.filterNot(kb.modelFiles.contains).map(f => Path.of(f).toAbsolutePath.normalize)
        .filterNot(p => governedExplicitly.exists(g => p == g || p.startsWith(g)))
    }
    val files = n.governs.map(ws.root.resolve) ++ impl
    if files.isEmpty then None else Some(Code.of(ws.root, files))

  /** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`, each with a
    * status and a detail. `complete`: `proven`, `open`, `failed`; each part: `needed` or `not-needed`;
    * `clash`: `no-clash` or `clash`; any of them `unchecked`, `timeout` or `informal` when not checked. Null
    * for a node with no parts. `needed` and `no-clash` are tries that found no proof: nothing is shown wrong,
    * nothing is proven.
    */
  def split(n: Node[?]): Option[Split] =
    import ObligationStatus.*
    val parts = kb.parts(n)
    def all(o: Outcome) = Split(o, parts.map(p => Split.Part(id(p), o.status, o.detail)), o)
    if parts.isEmpty || !kb.isStatement(n) then None
    else if generate.splitParts(n).isEmpty then Some(all(Outcome(Informal, "not formalized: decided by reading")))
    else current(n) match
      case None =>
        val c = checks.get(id(n))
        val why = c.filter(_.status == CheckStatus.Waiting).flatMap(_.messages.headOption)
          .orElse(c.filter(_.status == CheckStatus.Timeout).map(_ => "Lean timed out: run check again"))
          .getOrElse(if c.isDefined then "changed since the last check" else "not checked yet")
        Some(all(c.map(_.status) match
          case Some(CheckStatus.Timeout) => Outcome(Timeout, why)
          case Some(CheckStatus.ModelError) => Outcome(Failed, "the model does not build: " + c.flatMap(_.messages.headOption).getOrElse(""))
          case _ => Outcome(Unchecked, why)))
      case Some(c) =>
        val complete = c.result("complete") match
          case Some(r) if r.status == Proven && c.obligations.exists(o => o.name == "feasible" && o.status != Proven) =>
            Outcome(Open, "its parts make it by an authored proof: prove `feasible` too (some world meets the parts), or give a proven implementation below")
          case Some(r) => Outcome(r.status, r.detail.linesIterator.nextOption().getOrElse(""))
          case None => Outcome(Failed, c.messages.headOption.getOrElse("the check failed"))
        val needed = parts.map(p => c.result(if parts.size == 1 then "vacuous" else s"needed_${p.id}")
          .fold(Split.Part(id(p), Unchecked, "not checked"))(r => Split.Part(id(p), r.status, r.detail)))
        Some(Split(complete, needed, c.result("clash").fold(Outcome(Unchecked, "not checked"))(Outcome.of)))

  // ---------------------------------------------------------------------------
  // Decisions
  // ---------------------------------------------------------------------------

  /** Applies a decision (see `Decisions.decide`) to a fresh snapshot and records it: for programs and
    * tests.
    */
  def decide(r: DecisionRequest): Either[String, Unit] =
    val files = kb.nodes.flatMap(code).flatMap(_.files).distinct
    def known(s: String) = Option(s).filter(_.nonEmpty)
    Decisions.decide(baseSnapshot, ledger, r, java.time.Instant.now.toString, known(Git.head(ws.root)), known(Git.snapshot(ws.root, files)))
      .map(LedgerStore.save(ws.ledgerFile, _))

  /** Warnings about the record (decisions not signed by the developer) and the code. */
  def integrity: List[String] = Signing.warnings(ws.ledgerFile, ledger) ++ codeWarnings

  /** Warnings about the model and the code (the ledger's are read live, see `Signing.warnings`). */
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
    missing ++ owners ++ ideaCoverage ++ orphans ++
      ungoverned.map(f => s"$f is governed by no node: govern it (a design node) or move it")

  /** What doing nothing is, when it meets the root (Lean proved it). */
  /** An example of the contract, evaluated in Lean (not a probe, nor its code's run). */
  private def isExample(r: Result): Boolean = ObligationName.parse(r.name).exists { case ObligationName.Eval(_) => true; case _ => false }

  def idleOf(n: Node[?]): Option[String] = current(n).flatMap(_.result("idle")).filter(_.status == ObligationStatus.Idle).map(_.detail)

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
  def state(n: Node[?]): ReviewState = annotated.byId.get(id(n)).fold(ReviewState.Proposed)(_.state)

  def gone: List[NodeId] = annotated.gone.map(_.id)

  /** Creates the proof file of a node with a stub for its obligation. */
  def scaffold(n: Node[?]): Boolean =
    val g = generate
    val path = ws.lean.resolve(g.layout.proofs(n.id).path)
    // The obligations the last check left open (`complete`, the implementation, a check...), or
    // `complete` before any check: a stub each, added to the proof file (created if missing).
    val names = g.obligations(n).map(_.name)
    val open = checks.get(id(n)).toList.flatMap(_.obligations).filter(r => r.status == ObligationStatus.Open || r.status == ObligationStatus.Failed)
      .flatMap(r => ObligationName.parse(r.name)).filter(names.contains)
    val wanted = if open.nonEmpty then open else g.obligation(n, ObligationName.Complete).map(_.name).toList
    val existing = read(path).fold(List.empty[String])(src => Lean.theorems(src).map(_.name))
    val add = wanted.filterNot(o => existing.contains(o.lean))
    // Each stub shows, as a comment, the goal its first steps leave: the state `check` prints.
    val lake = Lake(ws.lean)
    val built = add.nonEmpty && lake.available && lake.build(g.layout.spec(n.id).name).ok
    def state(o: ObligationName) = Option.when(built)(proofState(n, o, g, lake)).flatten.fold("") { st =>
      s"  /- The goal here (as `check` prints it when automation gives up):\n${st.replace("-/", "- /").linesIterator.map("     " + _).mkString("\n")}\n  -/\n"
    }
    if add.isEmpty then false
    else read(path) match
      case None => write(path, g.proofFile(n, add, state))
      case Some(src) =>
        val end = s"end ${kb.name}.${n.id}.Proofs"
        val i = src.lastIndexOf(end)
        if i < 0 then false else write(path, src.substring(0, i) + g.stubs(add, state) + src.substring(i))

  /** The goal an obligation leaves after the first steps of a proof by hand (`Generate.recipe`), as
    * Lean prints it: what `scaffold` writes in a stub, and `check` prints when automation gave up, so
    * the agent starts from the state its own first steps give. None when Lean cannot say.
    */
  def proofState(n: Node[?], o: ObligationName, g: Generate, lake: Lake): Option[String] =
    val file = Files.createTempFile("frflow-state", ".lean")
    try
      Files.writeString(file, g.goalFile(n, o))
      val run = lake.elaborate(file.toString)
      val errs = Lean.diagnostics(run.output).filter(d => d.isError && d.file.endsWith(file.getFileName.toString))
      errs.find(_.message.startsWith("unsolved goals")).map(_.message.stripPrefix("unsolved goals").trim)
        .orElse(Option.when(errs.isEmpty && run.ok)("no goals: these steps prove it"))
    finally Files.deleteIfExists(file)

  private def stateText(o: ObligationName, state: String): String =
    s"After `${Generate.recipe(o).mkString("; ")}` (the first steps the stub has), the goal is:\n$state"

  def tree: String = Reports.tree(annotated)

  /** The tree and its warnings, and whether the knowledge base is complete (the CI gate). */
  def status: (String, Boolean) =
    val a = annotated
    val warnings = integrity ++ uncrossed ++ restated
    val ok = Reports.complete(a) && warnings.isEmpty
    // What each invariant does not reach (by the type of what a contract returns), so a gap is seen.
    val notes = kb.nodes.filter(_.isInvariant).flatMap { i =>
        val out = kb.nodes.filter(c => c.kind == NodeKind.Contract && !kb.inScope(i).contains(c))
        Option.when(out.nonEmpty)(s"${i.id} does not reach ${out.map(c => s"${c.id} (returns ${c.post.flatMap(_.params.lastOption).fold("?")(_._2)})").mkString(", ")}: its rule is about none of what they return")
      }
    (Reports.tree(a) + "\n\n" + trustedLine + coverage + "\n" + Reports.load(a) + notes.map("note: " + _ + "\n").mkString + warnings.map("warning: " + _ + "\n").mkString +
      (if ok then "Every node is accepted, proven (or decided by reading, where it opted out of Lean), and its examples pass."
       else "Not every node is accepted, proven, and passing its examples, or there are warnings.") + "\n", ok)

  /** What the root rests on, of the code: the hypotheses of `root_impl`. */
  def trustedLine: String =
    val g = generate
    kb.root.filter(g.formal).fold("") { r =>
      val st = current(r).flatMap(_.result("root_impl")).fold("not checked")(_.status.toString)
      s"Trusted (the hypotheses of root_impl, $st): ${if g.trusted.isEmpty then "nothing" else g.trusted.map(t => s"${t.id} (${Workflow.shownKind(t)})").mkString(", ")}.\n"
    }

  /** How far the proofs reach: splits proven, splits out of Lean, and contracts proven down to their
    * code (a proven define, with any running code checked against it), checked by running only, or
    * reviewed only. What the experiment measures.
    */
  def coverage: String =
    val splits = kb.nodes.filter(n => kb.isStatement(n) && kb.parts(n).nonEmpty)
    def provenSplit(n: Node[?]) = split(n).exists(_.proven)
    val formalSplits = splits.filter(n => generate.splitParts(n).isDefined)
    val proven = formalSplits.filter(provenSplit)
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    val down = provenDown
    val plain = contracts.filter(c => kb.implementation(c).exists(_.proven.isEmpty))
    val beside = down.flatMap(c => kb.implementation(c).filter(_.wiring.nonEmpty).map(i =>
      s"${c.id}: proven define ${i.proven.get.name}; running code ${Reports.runningCode(i.wiring)} checked against it"))
    val designs = kb.nodes.filter(_.kind == NodeKind.Design)
    s"Proofs: ${proven.size} of ${splits.size} splits proven in Lean" +
      s"${if formalSplits.diff(proven).nonEmpty then s" (${formalSplits.diff(proven).map(_.id).mkString(", ")} not proven yet)" else ""}" +
      s"${if splits.diff(formalSplits).nonEmpty then s" (${splits.diff(formalSplits).map(_.id).mkString(", ")} out of Lean)" else ""}; " +
      s"${down.size} of ${contracts.size} contracts proven down to their code" +
      (if beside.nonEmpty then s" (${beside.mkString("; ")})" else "") +
      (if plain.nonEmpty then s", checked by running for ${plain.map(_.id).mkString(", ")}" else "") +
      (if designs.nonEmpty then s"; ${designs.size} design decision(s) govern code reviewed only (${designs.map(_.id).mkString(", ")})" else "") +
      evaluated + ".\n"

  /** How many examples Lean evaluated as Scala does (the translation's cross-check), and where none. */
  private def evaluated: String =
    val per = kb.nodes.filter(c => c.post.isDefined && generate.formal(c) && c.cases.nonEmpty).map { c =>
      val rs = current(c).toList.flatMap(_.obligations)
      (c, rs.count(o => isExample(o) && o.status == ObligationStatus.Proven), c.cases.size)
    }
    val probes = kb.nodes.flatMap(c => current(c).toList.flatMap(_.obligations)).count(o => ObligationName.parse(o.name).exists(_.isProbe) && o.status == ObligationStatus.Proven)
    if per.isEmpty then ""
    else
      val none = per.filter((_, ok, _) => ok == 0).map(_._1.id)
      s"; examples evaluated in Lean as in Scala: ${per.map(_._2).sum} of ${per.map(_._3).sum}, and $probes probe(s) near them" +
        (if none.nonEmpty then s" (none for ${none.mkString(", ")}: unchecked, or its parameters are functions)" else "")

  /** The contracts proven down to their code: their implementation is a proven define, proven to meet
    * them (running code beside it, if any, is checked against it).
    */
  def provenDown: List[Node[?]] =
    kb.nodes.filter(c => c.kind == NodeKind.Contract && generate.provenImpl(c).isDefined &&
      current(c).exists(k => k.status == CheckStatus.Proven && k.result("impl").exists(_.status == ObligationStatus.Proven)))

  /** One-part nodes Lean proves say what their part says (`restates`, with `complete` proven): a node
    * that only restates its part is not a node.
    */
  def restated: List[String] =
    kb.nodes.flatMap(n => current(n).toList.filter(_.result("complete").exists(_.status == ObligationStatus.Proven))
      .flatMap(_.result("restates")).filter(_.status == ObligationStatus.Restates).map(_.detail))

  /** Formal contracts whose translation no example cross-checks: checked, and none of their examples
    * evaluated in Lean as in Scala.
    */
  def uncrossed: List[String] =
    kb.nodes.filter(c => c.kind == NodeKind.Contract && generate.formal(c) && c.cases.nonEmpty).flatMap { c =>
      current(c).filter(k => !k.obligations.exists(o => isExample(o) && o.status == ObligationStatus.Proven)).map(_ =>
        s"${c.id}: none of its examples is evaluated in Lean, so nothing checks that the Lean means what the Scala does: give its parameters values Lean has (bindTable for a lookup)")
    }

  /** Open requests from the developer. */
  def requests: List[Request] = allRequests.filter(_.status == RequestStatus.Open)
  def allRequests: List[Request] = RequestStore.load(ws.requestsFile)

  /** Everything known about a node (docs/DAG.md §7): its idea section, the vocabulary it uses (terms,
    * meanings, definitions in force), the nodes above it with their reasons, the co-parts under each
    * parent, its parts, the alternatives rejected, what moved, and what the developer asked for. This is
    * what a fresh agent, or a new engineer, reads first.
    */
  def context(n: Node[?]): String =
    val g = generate
    val l = ledger
    val ann = annotated
    val st: Map[String, String] = ann.nodes.map(r => r.id.value -> r.state.toString).toMap
    val sb = StringBuilder()
    val section = (n :: kb.ancestors(n)).find(_.ideaSection.trim.nonEmpty)
    val ideaText = Decisions.ideaSections(ideaDecided)._1 + section.fold("")(s => "\n\n" + ideaOf(s)) +
      (if notModelled.nonEmpty then s"\n\n## Not modelled\n\n$notModelled" else "")
    sb ++= s"# ${kb.name} / ${n.id}\n\n## Idea (${section.fold("its purpose")(s => s"the section ${s.ideaSection}")})\n\n${ideaText.trim}\n\n"
    def kind(x: Node[?]) = Workflow.shownKind(x)
    // Every decision on the node, oldest first, each marked if given for an earlier version of what it says.
    def reasons(a: Node[?]): Unit =
      val nowHash = hash(a)
      def ver(d: Decision) = if d.hash == nowHash || !d.action.binds then "" else " [given for an earlier version of it]"
      def line(d: Decision) = d.action match
        case Action.Accept if l.chosen(id(a)).contains(d) => s"Chosen by ${d.by} because: ${d.reason}"
        case Action.Accept  => s"Change accepted by ${d.by}: ${d.reason}"
        case Action.Confirm => s"Confirmed by ${d.by}: ${d.reason}"
        case Action.Revisit => s"To revisit (${d.by}): ${d.reason}"
        case Action.Reject  => s"Rejected by ${d.by} at ${d.at}: ${d.reason}"
        case other          => s"${other.toString.capitalize} by ${d.by}: ${d.reason}"
      l.history(id(a)).foreach(d => sb ++= s"${line(d)}${ver(d)}\n\n")
      l.alternatives(id(a)).foreach((alt, c) => sb ++= s"- Rejected alternative $alt: ${c.statement} (why: ${c.why})\n")
    def src(label: String, x: Lifted[?]) = sb ++= s"$label:\n```scala\n${x.source}\n```\n"
    def show(a: Node[?]) =
      sb ++= s"### ${a.id} (${kind(a)}) [${st.getOrElse(a.id, "?")}]\n\n${a.statement}\n\nWhy: ${a.why}\n\n"
      reasons(a)
      a.formula.foreach(src("formula", _))
      a.post.foreach(src(s"post (of every call of ${a.op.fold("")(_.name)})", _))
      a.rule.foreach(src("rule", _))
      a.substs.foreach(s => sb ++= s"- `${s.name} := ${s.term.fold(s.lean)(_.source)}`\n")
      kb.limits(a).foreach(x => sb ++= s"- does not promise: $x\n")
      if kb.root.exists(_ eq a) then idleOf(a).foreach(w => sb ++= s"- doing nothing meets it ($w): it says only what must not happen; state what users can do\n")
      kb.exampleResults(a).foreach(r => sb ++= s"- example: ${r.example.describe} [${r.verdict}]\n")
      code(a).foreach(c => sb ++= s"- governs: ${c.files.mkString(", ")}\n")
      content(a).str("implementation").foreach(i => sb ++= s"implementation:\n```scala\n$i\n```\n")
      sb ++= "\n"
    // What its terms mean: the open terms, and the definitions in force (as decided).
    val used = kb.definitionsUsed(n, g.inForce)
    sb ++= "## Vocabulary it uses\n\n"
    vocabulary(n).foreach(v => sb ++= s"- $v\n")
    used.foreach(d => sb ++= s"- defined by ${d.id} [${st.getOrElse(d.id, "?")}]: ${d.statement} ${d.substs.map(s => s"`${s.name} := ${s.term.fold(s.lean)(_.source)}`").mkString(", ")}\n")
    val defs = Def.closure((n :: used).flatMap(_.referenced).flatMap(_.defs))
    defs.foreach(d => sb ++= s"```scala\n${d.name} = ${d.lifted.source}\n```\n")
    sb ++= "\n"
    // The nodes above, nearest first, each once.
    val above = kb.ancestors(n)
    if above.nonEmpty then
      sb ++= "## Above it (what it helps prove), nearest first\n\n"
      above.foreach(show)
    sb ++= "## The node\n\n"
    show(n)
    // Under each parent: the other parts, which together with this one make it, and those rejected there.
    kb.parentsOf(n).foreach { p =>
      val beside = kb.parts(p).filterNot(_ eq n)
      val rejected = l.rejectedUnder(id(p)).filterNot((r, _, _) => r == id(n) || beside.exists(b => id(b) == r))
      if beside.nonEmpty || rejected.nonEmpty then
        sb ++= s"## Beside it, under ${p.id} (its co-parts: together they make ${p.id})\n\n"
        beside.foreach(o => sb ++= s"- ${o.id} (${kind(o)}) [${st.getOrElse(o.id, "?")}]: ${o.statement}\n")
        rejected.foreach((r, c, why) => sb ++= s"- rejected ${r}: ${c.statement} — rejected because: $why\n")
        sb ++= "\n"
    }
    val parts = kb.children(n)
    if parts.nonEmpty then
      sb ++= s"## Its parts (a change here may affect them)\n\n"
      parts.foreach { c =>
        sb ++= s"- ${c.id} (${kind(c)}) [${st.getOrElse(c.id, "?")}]: ${c.statement} Why: ${c.why}\n"
        l.chosen(id(c)).foreach(d => sb ++= s"  Chosen by ${d.by} because: ${d.reason}\n")
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
        sb ++= s"### ${i.id} (invariant) [${st.getOrElse(i.id, "?")}]\n\n${i.statement}\n\nWhy: ${i.why}\n\n"
        i.rule.foreach(r => sb ++= s"rule:\n```scala\n${r.source}\n```\n")
        kb.nodes.flatMap(c => c.kept.filter(_.invariant eq i).map(c -> _)).foreach { (c, k) =>
          sb ++= k.view.fold(s"- ${c.id} is exempt: ${k.exempt}\n")(v => s"- kept by ${c.id}, showing the rule: `${v.source}`\n")
        }
        sb ++= "\n"
      }
    ann.byId.get(id(n)).filter(_.review.causes.nonEmpty).foreach { me =>
      val causes = me.review.causes
      sb ++= s"## What moved since ${n.id} was decided: ${causes.mkString(", ")}\n\n"
      def fields(before: Content, now: Content): String =
        def flat(c: Content): Map[String, String] = c.fields.map((k, v) =>
          k -> v.asString.orElse(v.asArray.map(_.map(x => x.asString.getOrElse(Canonical.print(x))).mkString("\n"))).getOrElse(Canonical.print(v))).toMap
        val (b, a) = (flat(before), flat(now))
        def indent(t: String) = t.linesIterator.mkString("\n      ")
        (b.keySet ++ a.keySet).toList.sorted.filter(k => b.get(k) != a.get(k)).map { k =>
          s"  - $k\n    was: ${indent(b.getOrElse(k, ""))}\n    now: ${indent(a.getOrElse(k, ""))}\n"
        }.mkString
      if causes.contains(Cause.Self) then
        l.binding(id(n)).foreach(d => sb ++= s"- ${n.id} itself changed:\n${fields(d.content, me.node.content)}")
      me.review.moved.foreach { m =>
        val now = ann.byId.get(m.id).fold(Content.empty)(_.node.content)
        sb ++= s"- the meaning of ${m.id} changed:\n${fields(m.before, now)}"
      }
      kb.parentsOf(n).filter(p => st.get(p.id).contains("rejected")).foreach(p => sb ++= s"- its parent ${p.id} was rejected: move it under the node chosen instead\n")
      if causes.contains(Cause.Revisit) then
        l.current(id(n)).filter(_.action == Action.Revisit).foreach(r => sb ++= s"- ${r.by} asked to revisit it: ${r.reason}\n")
      if causes.contains(Cause.Code) then
        val since = l.binding(id(n)).flatMap(d => d.tree.filter(Git.has(ws.root, _)).orElse(d.commit)).getOrElse("")
        val d = code(n).fold("")(c => Git.diff(ws.root, since, c.files))
        sb ++= (if d.nonEmpty then s"- the code it governs changed:\n```diff\n$d```\n" else "- the code it governs changed (no git diff available)\n")
      sb ++= "\n"
    }
    g.obligations(n).foreach { o =>
      val stl = current(n).flatMap(_.result(o.name.lean)).fold("not checked")(r => s"${r.status}${if r.detail.nonEmpty then s" (${r.detail.linesIterator.next()})" else ""}")
      sb ++= s"## Obligation ${o.name} of ${n.id} [$stl]\n\n${o.description}\n\n```lean\n${o.statement}\n```\n\n"
    }
    // What the last check left open or failed, with Lean's message in full (the goal it stopped at).
    current(n).orElse(checks.get(id(n))).foreach { c =>
      val bad = c.obligations.filter(!_.fine)
      if bad.nonEmpty || c.messages.nonEmpty then
        sb ++= s"## Last check of ${n.id}: ${c.status}${if current(n).isEmpty then " (before the latest change)" else ""}\n\n"
        bad.foreach(r => sb ++= s"- ${r.status} ${r.name}:\n```\n${r.detail}\n```\n")
        c.messages.foreach(m => sb ++= s"- $m\n")
        sb ++= "\n"
    }
    val asks = allRequests.filter(_.node.contains(id(n)))
    if asks.nonEmpty then
      sb ++= "## Requests from the developer\n\n"
      asks.foreach(r => sb ++= s"- [${r.id}, ${r.status}] ${r.text}${r.answer.filter(_.nonEmpty).fold("")(a => s"\n  Answer: $a")}\n")
      sb ++= "\n"
    sb ++= s"A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.\nThe developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).\n"
    sb.result()

  // ---------------------------------------------------------------------------
  // Snapshot: what agents read
  // ---------------------------------------------------------------------------

  /** The knowledge base as data, from the Scala definitions and the checks; without decisions. */
  def baseSnapshot: Snapshot =
    import ObligationStatus.*
    val g = generate
    def node(n: Node[?]): SnapNode =
      val check = current(n)
      def res(name: String) = check.flatMap(_.result(name))
      def outcome(name: String) = res(name).fold(Outcome.unchecked)(Outcome.of)
      val isRoot = kb.root.exists(_ eq n)
      val c = content(n)
      SnapNode(
        id = id(n),
        kind = Workflow.kindOf(n),
        content = c,
        hash = c.hash,
        parents = ids(kb.parentsOf(n)),
        parts = ids(kb.children(n)),
        replaces = n.replaced.map(id),
        op = n.op.map(_.name),
        defines = n.defines,
        uses = ids(kb.definitionsUsed(n, g.inForce)),
        relies = ids(g.callees(n)),
        rule = n.isInvariant,
        limits = kb.limits(n),
        // The root met by doing nothing: it says only what must not happen (see `Reports.unproven`).
        idle = Option.when(isRoot)(idleOf(n)).flatten,
        status = Option.when(kb.isStatement(n))(if !g.formal(n) then CheckStatus.Informal
          else check.orElse(checks.get(id(n)).filter(_.hash == checkHash(n))).fold(CheckStatus.Unchecked)(_.status)),
        leaf = n.kind == NodeKind.Claim && kb.parts(n).isEmpty,
        examples = kb.exampleResults(n).zipWithIndex.map { (r, i) =>
          // What Lean computes of the example, against what Scala does (the examples written, not generated ones).
          def lean(name: String) = Option.when(i < n.cases.size && g.formal(n))(outcome(name))
          ExampleView(r.example.note, r.example.givens, r.example.call, r.example.expected, r.contract, r.implementation,
            lean(ObligationName.Eval(i).lean), if g.provenImpl(n).isEmpty then None else lean(ObligationName.EvalImpl(i).lean))
        },
        code = code(n),
        split = split(n),
        invariants = n.kept.map { k =>
          val (st, detail) =
            if k.view.isEmpty then (Exempt, k.exempt)
            else if !g.formalKeeps(n).exists(_._1 eq k.invariant) then (Informal, "checked on the examples and at run time; not formalized")
            else
              // Kept: what is proven, that the view lists all the result holds of it, and the invariant's
              // `complete`, this contract among its parts. Lean proving the invariant holds without it
              // (`not-needed`) leaves it `open`; a try that found no proof (`needed`) proves nothing, and is said apart.
              val inv = split(k.invariant)
              val cover = res(s"cover_${k.invariant.id}").map(r => (r.status, s"coverage: ${r.detail}"))
              val complete = inv.map(s => (s.complete.status, s.complete.detail))
              val needed = inv.flatMap(_.needed.find(_.id == id(n))).map(p => (p.status, p.detail))
              val notNeeded = needed.filter(_._1 == NotNeeded).map(c => (Open, c._2))
              (cover.toList ++ complete ++ notNeeded).find(_._1 != Proven).getOrElse(complete.fold((Unchecked, "not checked yet"))(_ => (Proven,
                s"${k.invariant.id} follows from the contracts that keep it, ${n.id} among them" +
                  needed.filter(_._1 == Needed).fold("")(x => s"; needed: not shown otherwise — ${x._2}"))))
          Kept(id(k.invariant), k.view.fold("")(_.source), k.invariant.rule.fold("")(_.source), st, detail)
        },
        expectations = n.expected.zipWithIndex.map { case ((st, l), i) =>
          val o = if !g.formal(n) then Outcome(Informal, "not formalized") else outcome(ObligationName.Expect(i).lean)
          Expectation(st, l.source, o.status, o.detail)
        },
        implementationProof = kb.implementation(n).flatMap(_.proven).map { d =>
          val o = if !g.formal(n) then Outcome(Informal, "the contract is out of Lean: checked on the examples and at run time") else outcome("impl")
          ImplProof(d.name, o.status, o.detail)
        },
        rootImpl = Option.when(isRoot && g.formal(n))(outcome("root_impl")),
        covers = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.nonEmpty))),
        exempts = if !n.isInvariant then Nil else ids(kb.nodes.filter(_.kept.exists(k => (k.invariant eq n) && k.view.isEmpty))),
        obligations = if !g.formal(n) then Nil else g.obligations(n).map(o => ObligationText(o.name.lean, o.statement, o.description)),
        proof = read(ws.lean.resolve(g.layout.proofs(n.id).path)).map(src => ProofFile("lean/" + g.layout.proofs(n.id).path, src)),
        holds = if g.formal(n) then g.holdsStatement(n) else "",
        lean = if g.formal(n) then g.spec(n) else "",
        messages = check.orElse(checks.get(id(n)).filter(_.status == CheckStatus.Waiting)).toList.flatMap(_.messages))
    Snapshot(
      name = kb.name,
      nodes = kb.ordered.map(node),
      idea = idea,
      ideaFile = kb.idea,
      warnings = codeWarnings ++ uncrossed ++ restated,
      root = kb.root.map(id),
      definitions = ids(kb.definitions),
      trusted = if kb.root.exists(g.formal) then ids(g.trusted) else Nil,
      exportedAt = java.time.Instant.now.toString,
      opaques = kb.opaques.map(o => OpaqueTerm(o.name, o.means, g.inForce.get(o.name).map(id))),
      params = kb.params.map(p => ParamTerm(p.name, p.means, kb.isOp(p.name), g.inForce.get(p.name).map(id),
        kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).toMap.getOrElse(p.name, ""))),
      types = kb.types.map(t => TypeText(t.name, t.lean)),
      defs = kb.defs.map(d => DefText(d.name, d.lifted.source)))

  /** The snapshot with the developer's decisions. */
  def annotated: Annotated = Decisions.annotate(baseSnapshot, ledger)

  /** Writes the snapshot to `.frflow/kb.json`. */
  def writeSnapshot(): Path =
    Store.write(ws.snapshotFile, Canonical.file(baseSnapshot.asJson) + "\n")
    ws.snapshotFile

object Workflow:
  /** A node's kind, as the snapshot names it. */
  def kindOf(n: Node[?]): Kind = Kind.valueOf(n.kind.toString)
  /** A node's kind as people read it: an invariant is a claim with a rule. */
  def shownKind(n: Node[?]): String = kindOf(n).shown(n.isInvariant)
  /** How checks are run and read: a change to it re-runs every check. */
  val CheckerVersion: Int = 6
