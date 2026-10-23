package frflow
package check

import frflow.lean.*
import frflow.protocol.{NodeKind as _, *}
import frflow.protocol.ObligationStatus.{Failed, Open, Proven, Unevaluated}
import java.time.Instant

/** What a check of a node finds, before it is stamped with its hash and time. */
final case class Judged(status: CheckStatus, results: List[Result], messages: List[String], axioms: List[String] = Nil):
  /** With the examples evaluated in Lean: every result carries them. */
  def withEvaluations(rs: List[Result]): Judged = copy(results = results ++ rs)
  def stamp(hash: Hash, at: Instant): NodeCheck = NodeCheck(hash, status, results, messages, axioms, at.toString)

/** One run of Lean on one file, read: the theorems it holds, and what Lean said of each (fail closed: no
  * audit, no proof).
  */
final case class Elaborated(run: Run, src: String, rel: String):
  val theorems: List[Lean.Decl] = Lean.theorems(src)
  /** What Lean said of the file. */
  val diagnostics: List[Diagnostic] = Lean.diagnostics(run.output).filter(_.file.endsWith(rel))
  private val ax = Lean.axioms(run.output)
  private def lines(name: String) = theorems.find(_.name == name).map(d => (l: Int) => l >= d.from && l <= d.to)
  /** The theorem is there, and Lean reports no error in it. */
  def proves(name: String): Boolean = lines(name).exists(in => !diagnostics.exists(x => x.isError && in(x.line)))
  def axiomsOf(name: String): Option[List[String]] = ax.collectFirst { case (t, as) if t == name || t.endsWith("." + name) => as }
  /** Why a theorem does not hold: none when Lean reports no error in it, no `sorry`, and its axioms. */
  def why(name: String): Option[String] = lines(name) match
    case None => Some(s"no theorem $name")
    case Some(in) =>
      diagnostics.find(x => x.isError && in(x.line)).map(_.message.linesIterator.filterNot(_.contains("depends on axioms")).mkString("\n").take(20000))
        .orElse(Option.when(diagnostics.exists(x => x.isSorry && in(x.line)) || axiomsOf(name).exists(_.contains("sorryAx")))("uses sorry"))
  def holds(name: String): Boolean = why(name).isEmpty

/** The judges of a check: from the recorded runs of Lean to a verdict, without running anything. Each
  * returns the verdict that ends the check there, if any (see `NodeChecker` for the order they run in).
  */
object Verdict:
  val NoAudit = "<no audit result>"

  /** Lean's errors in a run, or its last lines. */
  def errors(r: Run): List[String] =
    val ds = Lean.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
    if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))

  private def failed(msg: String): Judged = Judged(CheckStatus.Failed, Nil, List(msg))
  private def notAllowed(src: String): List[String] = Lean.violations(src).map(_._2).distinct

  /** Two definitions of a term it uses, neither chosen: what it says is not known yet. */
  def waiting(kb: KnowledgeBase, g: Generate, n: Node[?]): Option[Judged] =
    val waits = g.waitsForDefinition(n)
    Option.when(waits.nonEmpty)(Judged(CheckStatus.Waiting, Nil, List(
      s"waits for the choice between the definitions of ${waits.mkString(", ")} (${waits.flatMap(t => kb.definitionsOf(t).map(_.id)).mkString(", ")})")))

  /** The model built. A timeout is not a broken model: the machine was busy, or Lean slow; it is checked again. */
  def model(spec: Run): Option[Judged] = spec match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List("Lean timed out building the model (the machine may be busy): run check again")))
    case r if !r.ok => Some(Judged(CheckStatus.ModelError, Nil, errors(r)))
    case _ => None

  /** The lemmas a proof file imports, shared by the proof files: the same filter. Whether to build them. */
  def lemmas(g: Generate, proof: String, lemmas: Option[String]): Either[Judged, Boolean] =
    val imports = Lean.lemmaImports(proof)
    if imports.isEmpty then Right(false)
    else if imports != List(g.lemmasModule) then Left(failed(s"a proof file may import only ${g.lemmasModule}, not ${imports.mkString(", ")}"))
    else lemmas match
      case None => Left(failed(s"the proof imports ${g.lemmasModule}, but lean/${g.lemmasPath} does not exist"))
      case Some(src) =>
        val bad = notAllowed(src) ++ Lean.lemmaImports(src).map(m => s"import $m")
        if bad.nonEmpty then Left(failed(s"not allowed in lean/${g.lemmasPath}: ${bad.distinct.mkString(", ")}")) else Right(true)

  def lemmasBuilt(g: Generate, run: Run): Option[Judged] =
    if !run.ok then Some(Judged(CheckStatus.Failed, Nil, "the lemmas do not build" :: errors(run)))
    else Option.when(Lean.usesSorry(run.output))(failed(s"lean/${g.lemmasPath} uses sorry"))

  /** The examples, evaluated in Lean. Scala and Lean must agree on every one: what Scala computes of it,
    * Lean proves; its opposite, Lean does not.
    */
  def evaluations(evals: List[Generate#Eval], notEvaluated: List[(String, String)], e: Option[Elaborated]): List[Result] =
    e.toList.flatMap(e => evals.map(evaluation(_, e)))
      .filterNot(r => r.name.startsWith("probe") && r.status == Unevaluated) ++ // a probe Lean cannot decide says nothing
      notEvaluated.map((name, why) => Result(name, Unevaluated, why))

  private def evaluation(x: Generate#Eval, e: Elaborated): Result =
    (e.proves(x.name), e.proves(x.name + "_opposite")) match
      case _ if e.diagnostics.isEmpty && !e.run.ok => Result(x.name, Unevaluated, s"${x.what}: Lean did not run: ${e.run.output.take(20000)}")
      case (true, false) => Result(x.name, Proven, s"Lean agrees: ${x.claim}")
      case (false, true) => Result(x.name, Failed, s"${x.what}: Scala computes ${x.claim}, Lean proves ${x.opposite}")
      case (true, true) => Result(x.name, Failed, s"${x.what}: Lean proves both ${x.claim} and its opposite")
      case (false, false) => Result(x.name, Unevaluated, s"${x.what}: Lean decides neither ${x.claim} nor its opposite")

  /** A disagreement means the translation does not mean what the Scala does, and nothing proven of the
    * node is about the code.
    */
  def agree(n: Node[?], evaluated: List[Result]): Option[Judged] =
    val disagree = evaluated.filter(_.status == Failed)
    Option.when(disagree.nonEmpty)(Judged(CheckStatus.Failed, evaluated,
      s"Lean and Scala disagree on ${disagree.size} example(s) or probe(s): the Lean translation does not mean what the Scala does, so nothing proven of ${n.id} is about the code" :: disagree.map(_.detail)))

  /** A theorem of a file: proven when Lean reports no error in it and no `sorry`; an authored one must state
    * exactly its obligation and use only what a proof file may.
    */
  def judge(name: String, e: Elaborated, isAuthored: Boolean): Result =
    e.theorems.find(_.name == name) match
      case None => Result(name, Open, s"no theorem $name in ${e.rel}")
      case Some(d) =>
        def in(l: Int) = l >= d.from && l <= d.to
        val bad = if isAuthored then notAllowed(e.src) else Nil
        if d.statement != s"Obl.$name" then Result(name, Failed, s"must state exactly Obl.$name")
        else if bad.nonEmpty then Result(name, Failed, s"not allowed in a proof file: ${bad.mkString(", ")}")
        else e.diagnostics.find(x => x.isError && in(x.line)) match
          case Some(err) => Result(name, Open, err.message.take(20000))
          case None if e.diagnostics.exists(x => x.isSorry && in(x.line)) => Result(name, Open, "uses sorry")
          case None if !e.run.ok => Result(name, Open, "not checked: " + e.run.output.take(20000))
          case None => Result(name, Proven, if isAuthored then "authored" else "auto")

  /** Automation gave up on `complete`: what to do next, and the goal its first steps leave. */
  def gaveUp(g: Generate, n: Node[?], r: Result, state: Option[String]): Result =
    r.copy(detail = s"automation gave up: write theorem complete : Obl.complete in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)\n" +
      state.fold(s"Lean: ${r.detail}")(ProofState.text("complete", _)))

  /** An authored `impl` must state exactly its obligation, and use only what a proof file may. */
  def implRules(proof: String): Option[Result] =
    val bad = notAllowed(proof)
    if bad.nonEmpty then Some(Result("impl", Failed, s"not allowed in a proof file: ${bad.mkString(", ")}"))
    else Option.when(!Lean.theorems(proof).find(_.name == "impl").map(_.statement).contains("Obl.impl"))(Result("impl", Failed, "must state exactly Obl.impl"))

  /** The axioms `impl` rests on, from its build. */
  def implAxioms(run: Run): List[String] =
    Lean.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List(NoAudit))

  /** The code meets the contract, from what the contracts it calls promise: by an authored proof. */
  def implAuthored(run: Run): Result =
    if run.ok && !implAxioms(run).contains("sorryAx") then Result("impl", Proven, "authored")
    else if run.ok then Result("impl", Open, "uses sorry")
    else Result("impl", Open, s"not proven (authored): " + errors(run).take(3).mkString("\n").take(20000))

  /** ... or by automation; else what to do next, and the goal its first steps leave. */
  def implAuto(g: Generate, n: Node[?], run: Run, state: Option[String]): Result =
    if run.ok then Result("impl", Proven, "auto")
    else Result("impl", Open, s"not proven (auto): prove theorem impl : Obl.impl in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)\n" +
      state.fold("Lean: " + errors(run).take(3).mkString("\n").take(20000))(ProofState.text("impl", _)))

  /** The obligations judged: failed, open, or waiting for the parts (a node is proven with its parts). */
  def obligations(g: Generate, n: Node[?], split: List[Result], results: List[Result], parts: List[(String, Option[CheckStatus])]): Option[Judged] =
    val notYet = parts.filterNot(_._2.contains(CheckStatus.Proven))
    if results.exists(_.status == Failed) then Some(Judged(CheckStatus.Failed, results, Nil))
    else if split.exists(_.status == Open) then Some(Judged(CheckStatus.Open, results, List(s"prove it in lean/${g.proofsPath(n.id)} (run `scaffold ${n.id}`)")))
    else Option.when(notYet.nonEmpty)(Judged(CheckStatus.Waiting, results, List(s"waiting for its parts: ${notYet.map(_._1).mkString(", ")}")))

  def theorems(results: List[Result], run: Run): Option[Judged] = run match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, results, List("Lean timed out building the node's theorems: run check again")))
    case r if !r.ok => Some(Judged(CheckStatus.Failed, results, "the node's theorems do not build" :: errors(r)))
    case _ => None

  /** The proof file, when it proves obligations of the Checks file: whether to build it, or why it may not be. */
  def proofFile(g: Generate, n: Node[?], proof: String): Either[String, Boolean] =
    if !g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) then Right(false)
    else
      val bad = notAllowed(proof)
      if bad.nonEmpty then Left(s"not allowed in lean/${g.proofsPath(n.id)}: ${bad.mkString(", ")}") else Right(true)

  def proofFileBuilt(g: Generate, n: Node[?], run: Run): Option[String] =
    Option.when(!run.ok)(s"lean/${g.proofsPath(n.id)} does not build: " + errors(run).take(5).map(_.take(20000)).mkString("\n"))

  /** Everything else imports the proof file: what it proves fails, by name, and the file is the message. */
  def proofFileFails(g: Generate, n: Node[?], results: List[Result], why: String): Judged =
    Judged(CheckStatus.Failed, results ++ g.extraObligations(n).filter(o => g.isAuthored(n, o.name)).map(o => Result(o.name, Failed, why)), List(why))

  def checksRan(results: List[Result], run: Run): Option[Judged] = run match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, results, List("Lean timed out checking the node (the machine may be busy): run check again")))
    case _ => None

  /** The verdict from the node's Checks file, in one run of Lean (see `Generate.checks`), and the root's
    * `root_impl`: each theorem holds when Lean reports no error in it, no `sorry`, and its axioms.
    *
    * @param results the obligations judged so far (`complete`, `impl`)
    * @param impl    `impl`, with the axioms its build rests on
    */
  def finish(a: Analysis, n: Node[?], results: List[Result], impl: Option[(Result, List[String])], checks: Elaborated,
      root: Option[Elaborated]): Judged =
    val g = a.generate
    // The tries: what Lean proves of them says the node or its split says nothing, or too much.
    val tried = g.tries(n).map(t => (t, checks.holds(t.obligation.name)))
    val fatal = tried.collect { case (t, true) if t.kind.fatal => t.means }
    // Each in plain words: what Lean proved, or that it found no proof within the try's budget (see `TryKind`).
    lazy val idle = g.idleWhat(n)
    val one = g.splitParts(n).collect { case List(c) => c.id }.getOrElse("")
    val tries = tried.map { (t, proven) =>
      Result(t.obligation.name, if proven then t.kind.onProven else t.kind.onNot,
        if !proven then t.kind.unshown(n.id, one, idle) else if t.kind == TryKind.Idle then idle else t.means)
    }
    val extra = g.extraObligations(n).map { o =>
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      if o.name.startsWith("expect_") && tried.exists((t, p) => p && t.obligation.name == s"vacuous_${o.name}") then
        (Result(o.name, Failed, "it holds whatever the node says: it checks nothing"), Nil)
      else checks.why(o.name) match
        case None => (Result(o.name, Proven, how), checks.axiomsOf(o.name).getOrElse(List(NoAudit)))
        case Some("uses sorry") => (Result(o.name, Open, "uses sorry"), Nil)
        case Some(w) => (Result(o.name, Open, s"not proven ($how): prove theorem ${o.name} : Obl.${o.name} in lean/${g.proofsPath(n.id)}\nLean: $w"), Nil)
    }
    // A view whose coverage cannot be stated keeps nothing proven.
    val uncovered = g.formalKeeps(n).flatMap((i, _) => g.coverage(n, i).left.toOption.map(w =>
      Result(s"cover_${i.id}", Failed, s"what the view must list cannot be stated: $w")))
    val (rootImpl, rootAxioms) = root.map(rootOfCode(g, _)).unzip
    val used = (checks.axiomsOf("holds").getOrElse(List(NoAudit)) ++ extra.flatMap(_._2) ++
      impl.filter(_._1.status == Proven).toList.flatMap(_._2) ++ rootAxioms.toList.flatten).distinct.sorted
    val all = results ++ extra.map(_._1) ++ uncovered ++ tries ++ rootImpl
    if fatal.nonEmpty then Judged(CheckStatus.Failed, all, fatal, used)
    else if used.contains(NoAudit) then
      Judged(CheckStatus.Failed, all, List(s"Lean did not finish checking lean/${checks.rel}: " + errors(checks.run).take(3).map(_.take(5000)).mkString("\n")), used)
    else if used.exists(a => !Lean.allowedAxioms(a)) then
      Judged(CheckStatus.Failed, all, List(s"disallowed axioms: ${used.filterNot(Lean.allowedAxioms).mkString(", ")}"), used)
    // (What is left open is in the results, once: not repeated as messages.)
    else Judged(CheckStatus.Proven, all, Nil, used)

  /** The root, of the code: from what is trusted only. */
  private def rootOfCode(g: Generate, e: Elaborated): (Result, List[String]) =
    e.why("root_impl") match
      case None => (Result("root_impl", Proven, s"the root holds of the code, trusting ${if g.trusted.isEmpty then "nothing" else g.trusted.map(_.id).mkString(", ")}"),
        e.axiomsOf("root_impl").getOrElse(List(NoAudit)))
      case Some(w) => (Result("root_impl", Open, s"the root is not proven of the code: $w${if e.run.ok then "" else "\n" + errors(e.run).take(3).mkString("\n").take(5000)}"), Nil)
