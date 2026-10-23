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

/** One run of Lean on one file, and what Lean said of it (see `Elaboration`). */
final case class Elaborated(run: Run, lean: Elaboration):
  /** Why a theorem does not hold: none when Lean reports no error in it, no `sorry`, and its axioms. */
  def why(name: ObligationName): Option[String] = lean.verdict(name.lean).why(name.lean).map(_.take(20000))
  def holds(name: ObligationName): Boolean = why(name).isEmpty
  def axiomsOf(name: ObligationName): Option[List[String]] = lean.axiomsOf(name.lean)

/** The judges of a check: from the recorded runs of Lean to a verdict, without running anything. Each
  * returns the verdict that ends the check there, if any (see `NodeChecker` for the order they run in).
  */
object Verdict:
  val NoAudit = "<no audit result>"
  import ObligationName.{Complete, Impl, RootImpl}

  /** Lean's errors in a run, or its last lines. */
  def errors(r: Run): List[String] =
    val ds = LeanOutput.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
    if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))

  private def failed(msg: String): Judged = Judged(CheckStatus.Failed, Nil, List(msg))
  private def proofPath(g: Generate, n: Node[?]) = g.layout.proofs(n.id).path

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
    val imports = LeanSource.lemmaImports(proof)
    val module = g.layout.lemmas
    if imports.isEmpty then Right(false)
    else if imports != List(module.name) then Left(failed(s"a proof file may import only ${module.name}, not ${imports.mkString(", ")}"))
    else lemmas match
      case None => Left(failed(s"the proof imports ${module.name}, but lean/${module.path} does not exist"))
      case Some(src) => ProofRules.notAllowedInLemmas(src).map(bad => failed(s"not allowed in lean/${module.path}: $bad")).toLeft(true)

  def lemmasBuilt(g: Generate, run: Run): Option[Judged] =
    if !run.ok then Some(Judged(CheckStatus.Failed, Nil, "the lemmas do not build" :: errors(run)))
    else Option.when(LeanOutput.usesSorry(run.output))(failed(s"lean/${g.layout.lemmas.path} uses sorry"))

  /** The examples, evaluated in Lean. Scala and Lean must agree on every one: what Scala computes of it,
    * Lean proves; its opposite, Lean does not.
    */
  def evaluations(evals: List[Eval], notEvaluated: List[(ObligationName, String)], e: Option[Elaborated]): List[Result] =
    e.toList.flatMap(e => evals.map(x => x.name -> evaluation(x, e)))
      .filterNot((name, r) => name.isProbe && r.status == Unevaluated).map(_._2) ++ // a probe Lean cannot decide says nothing
      notEvaluated.map((name, why) => Result(name.lean, Unevaluated, why))

  private def evaluation(x: Eval, e: Elaborated): Result =
    val name = x.name.lean
    (e.lean.proves(name), e.lean.proves(name + "_opposite")) match
      case _ if e.lean.diagnostics.isEmpty && !e.run.ok => Result(name, Unevaluated, s"${x.what}: Lean did not run: ${e.run.output.take(20000)}")
      case (true, false) => Result(name, Proven, s"Lean agrees: ${x.claim}")
      case (false, true) => Result(name, Failed, s"${x.what}: Scala computes ${x.claim}, Lean proves ${x.opposite}")
      case (true, true) => Result(name, Failed, s"${x.what}: Lean proves both ${x.claim} and its opposite")
      case (false, false) => Result(name, Unevaluated, s"${x.what}: Lean decides neither ${x.claim} nor its opposite")

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
  def judge(o: ObligationName, e: Elaborated, isAuthored: Boolean): Result =
    val name = o.lean
    val bad = if isAuthored then ProofRules.notAllowed(e.lean.source) else None
    e.lean.theorem(name) match
      case None => Result(name, Open, s"no theorem $name in ${e.lean.file}")
      case Some(d) if d.statement != s"Obl.$name" => Result(name, Failed, s"must state exactly Obl.$name")
      case Some(_) if bad.nonEmpty => Result(name, Failed, s"not allowed in a proof file: ${bad.mkString}")
      case Some(_) => e.lean.verdict(name) match
        case TheoremVerdict.Proven if e.run.ok => Result(name, Proven, if isAuthored then "authored" else "auto")
        case TheoremVerdict.Proven => Result(name, Open, "not checked: " + e.run.output.take(20000))
        case v => Result(name, Open, v.why(name).getOrElse("").take(20000))

  /** Automation gave up on `complete`: what to do next, and the goal its first steps leave. */
  def gaveUp(g: Generate, n: Node[?], r: Result, state: Option[String]): Result =
    r.copy(detail = s"automation gave up: write theorem complete : Obl.complete in lean/${proofPath(g, n)} (run `scaffold ${n.id}`)\n" +
      state.fold(s"Lean: ${r.detail}")(ProofState.text(Complete, _)))

  /** An authored `impl` must state exactly its obligation, and use only what a proof file may. */
  def implRules(proof: String): Option[Result] =
    ProofRules.notAllowed(proof).map(bad => Result(Impl.lean, Failed, s"not allowed in a proof file: $bad"))
      .orElse(Option.when(!LeanSource.theorems(proof).find(_.name == Impl.lean).map(_.statement).contains("Obl.impl"))(
        Result(Impl.lean, Failed, "must state exactly Obl.impl")))

  /** The axioms `impl` rests on, from its build. */
  def implAxioms(run: Run): List[String] =
    LeanOutput.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }.getOrElse(List(NoAudit))

  /** The code meets the contract, from what the contracts it calls promise: by an authored proof. */
  def implAuthored(run: Run): Result =
    if run.ok && !implAxioms(run).contains("sorryAx") then Result(Impl.lean, Proven, "authored")
    else if run.ok then Result(Impl.lean, Open, "uses sorry")
    else Result(Impl.lean, Open, s"not proven (authored): " + errors(run).take(3).mkString("\n").take(20000))

  /** ... or by automation; else what to do next, and the goal its first steps leave. */
  def implAuto(g: Generate, n: Node[?], run: Run, state: Option[String]): Result =
    if run.ok then Result(Impl.lean, Proven, "auto")
    else Result(Impl.lean, Open, s"not proven (auto): prove theorem impl : Obl.impl in lean/${proofPath(g, n)} (run `scaffold ${n.id}`)\n" +
      state.fold("Lean: " + errors(run).take(3).mkString("\n").take(20000))(ProofState.text(Impl, _)))

  /** The obligations judged: failed, open, or waiting for the parts (a node is proven with its parts). */
  def obligations(g: Generate, n: Node[?], split: List[Result], results: List[Result], parts: List[(String, Option[CheckStatus])]): Option[Judged] =
    val notYet = parts.filterNot(_._2.contains(CheckStatus.Proven))
    if results.exists(_.status == Failed) then Some(Judged(CheckStatus.Failed, results, Nil))
    else if split.exists(_.status == Open) then Some(Judged(CheckStatus.Open, results, List(s"prove it in lean/${proofPath(g, n)} (run `scaffold ${n.id}`)")))
    else Option.when(notYet.nonEmpty)(Judged(CheckStatus.Waiting, results, List(s"waiting for its parts: ${notYet.map(_._1).mkString(", ")}")))

  def theorems(results: List[Result], run: Run): Option[Judged] = run match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, results, List("Lean timed out building the node's theorems: run check again")))
    case r if !r.ok => Some(Judged(CheckStatus.Failed, results, "the node's theorems do not build" :: errors(r)))
    case _ => None

  /** The proof file, when it proves obligations of the Checks file: whether to build it, or why it may not be. */
  def proofFile(g: Generate, n: Node[?], proof: String): Either[String, Boolean] =
    if !g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) then Right(false)
    else ProofRules.notAllowed(proof).map(bad => s"not allowed in lean/${proofPath(g, n)}: $bad").toLeft(true)

  def proofFileBuilt(g: Generate, n: Node[?], run: Run): Option[String] =
    Option.when(!run.ok)(s"lean/${proofPath(g, n)} does not build: " + errors(run).take(5).map(_.take(20000)).mkString("\n"))

  /** Everything else imports the proof file: what it proves fails, by name, and the file is the message. */
  def proofFileFails(g: Generate, n: Node[?], results: List[Result], why: String): Judged =
    Judged(CheckStatus.Failed, results ++ g.extraObligations(n).filter(o => g.isAuthored(n, o.name)).map(o => Result(o.name.lean, Failed, why)), List(why))

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
      Result(t.obligation.name.lean, if proven then t.kind.onProven else t.kind.onNot,
        if !proven then t.kind.unshown(n.id, one, idle) else if t.kind == TryKind.Idle then idle else t.means)
    }
    val extra = g.extraObligations(n).map { o =>
      val name = o.name.lean
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      val vacuous = o.name match
        case ObligationName.Expect(i) => tried.exists((t, p) => p && t.kind == TryKind.VacuousExpect(i))
        case _ => false
      if vacuous then (Result(name, Failed, "it holds whatever the node says: it checks nothing"), Nil)
      else checks.why(o.name) match
        case None => (Result(name, Proven, how), checks.axiomsOf(o.name).getOrElse(List(NoAudit)))
        case Some("uses sorry") => (Result(name, Open, "uses sorry"), Nil)
        case Some(w) => (Result(name, Open, s"not proven ($how): prove theorem $name : Obl.$name in lean/${proofPath(g, n)}\nLean: $w"), Nil)
    }
    // A view whose coverage cannot be stated keeps nothing proven.
    val uncovered = g.formalKeeps(n).flatMap((i, _) => g.coverage(n, i).left.toOption.map(w =>
      Result(ObligationName.Cover(i.id).lean, Failed, s"what the view must list cannot be stated: $w")))
    val (rootImpl, rootAxioms) = root.map(rootOfCode(g, _)).unzip
    val used = (checks.lean.axiomsOf("holds").getOrElse(List(NoAudit)) ++ extra.flatMap(_._2) ++
      impl.filter(_._1.status == Proven).toList.flatMap(_._2) ++ rootAxioms.toList.flatten).distinct.sorted
    val all = results ++ extra.map(_._1) ++ uncovered ++ tries ++ rootImpl
    if fatal.nonEmpty then Judged(CheckStatus.Failed, all, fatal, used)
    else if used.contains(NoAudit) then
      Judged(CheckStatus.Failed, all, List(s"Lean did not finish checking lean/${checks.lean.file}: " + errors(checks.run).take(3).map(_.take(5000)).mkString("\n")), used)
    else if used.exists(a => !ProofRules.allowedAxioms(a)) then
      Judged(CheckStatus.Failed, all, List(s"disallowed axioms: ${used.filterNot(ProofRules.allowedAxioms).mkString(", ")}"), used)
    // (What is left open is in the results, once: not repeated as messages.)
    else Judged(CheckStatus.Proven, all, Nil, used)

  /** The root, of the code: from what is trusted only. */
  private def rootOfCode(g: Generate, e: Elaborated): (Result, List[String]) =
    val name = RootImpl.lean
    e.why(RootImpl) match
      case None => (Result(name, Proven, s"the root holds of the code, trusting ${if g.trusted.isEmpty then "nothing" else g.trusted.map(_.id).mkString(", ")}"),
        e.axiomsOf(RootImpl).getOrElse(List(NoAudit)))
      case Some(w) => (Result(name, Open, s"the root is not proven of the code: $w${if e.run.ok then "" else "\n" + errors(e.run).take(3).mkString("\n").take(5000)}"), Nil)
