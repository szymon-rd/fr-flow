package frflow
package check

import cats.syntax.all.*
import frflow.lean.*
import frflow.protocol.*
import frflow.protocol.ObligationStatus.{Failed, Open, Proven, Shown, NotShown, Unevaluated}
import java.time.Instant

/** What a check of a node finds, before it is stamped with its hash and time. */
final case class Judged(status: CheckStatus, results: List[Result], messages: List[String], axioms: List[String] = Nil,
    hint: Option[String] = None):
  def withEvaluations(rs: List[Result]): Judged = copy(results = results ++ rs)
  def stamp(hash: Hash, at: Instant): NodeCheck = NodeCheck(hash, status, results, messages, axioms, at, hint)

/** One run of Lean on one file, and what Lean said of it (see `Elaboration`). */
final case class Elaborated(run: Run, lean: Elaboration):
  /** A run that failed with no error in this file (an import that did not build, Lean stopped) checked nothing in it. */
  def verdict(name: ObligationName): TheoremVerdict = lean.verdict(name.lean) match
    case TheoremVerdict.Proven if !run.ok && !lean.diagnostics.exists(_.isError) =>
      TheoremVerdict.Failed("not checked: " + Verdict.quoted(run))
    case v => v
  def axiomsOf(name: ObligationName): Option[List[String]] = lean.axiomsOf(name.lean)

/** The judges of a check, from the recorded runs of Lean, running nothing: each returns the verdict that ends it there, if any. */
object Verdict:
  import ObligationName.{Complete, Impl, RootImpl}

  /** Lean's output, cut to what a check records (`n`: to what a message quotes). */
  def clip(s: String, n: Int = 20000): String = s.take(n)

  /** The first errors of a run, as a message quotes them. */
  def quoted(r: Run): String = errors(r).take(3).map(clip(_, 5000)).mkString("\n")

  /** Lean's errors in a run, or its last lines. */
  def errors(r: Run): List[String] =
    val ds = LeanOutput.diagnostics(r.output).filter(_.isError).map(d => s"${d.file}:${d.line}: ${d.message}")
    if ds.nonEmpty then ds else List(r.output.linesIterator.toList.takeRight(15).mkString("\n"))

  def ruled(src: String, where: String): Option[String] = ProofRules.notAllowed(src).map(bad => s"not allowed in $where: $bad")

  private def failed(msg: String): Judged = Judged(CheckStatus.Failed, Nil, List(msg))
  private def proofPath(g: Generate, n: Node[?]) = s"lean/${g.layout.proofs(n.id).path}"
  private def scaffold(g: Generate, n: Node[?]) = s"prove it in ${proofPath(g, n)} (run `scaffold ${n.id}`)"

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

  /** Scala and Lean must agree on every example: Lean proves what Scala computes, not its opposite; an undecided probe says nothing. */
  def evaluations(evals: List[Eval], notEvaluated: List[(ObligationName, String)], e: Option[Elaborated]): List[Result] =
    e.toList.flatMap(e => evals.map(evaluation(_, e))).filterNot(r => r.name.isProbe && r.status == Unevaluated) ++
      notEvaluated.map((name, why) => Result(name, Unevaluated, why))

  private def evaluation(x: Eval, e: Elaborated): Result =
    val name = x.name.lean
    (e.lean.proves(name), e.lean.proves(name + "_opposite")) match
      case _ if e.lean.diagnostics.isEmpty && !e.run.ok => Result(x.name, Unevaluated, s"${x.what}: Lean did not run: ${clip(e.run.output)}")
      case (true, false) => Result(x.name, Proven, s"Lean agrees: ${x.claim}")
      case (false, true) => Result(x.name, Failed, s"${x.what}: Scala computes ${x.claim}, Lean proves ${x.opposite}")
      case (true, true) => Result(x.name, Failed, s"${x.what}: Lean proves both ${x.claim} and its opposite")
      case (false, false) => Result(x.name, Unevaluated, s"${x.what}: Lean decides neither ${x.claim} nor its opposite")

  /** A disagreement means the translation does not mean what the Scala does: nothing proven of the node is about the code. */
  def agree(n: Node[?], evaluated: List[Result]): Option[Judged] =
    val disagree = evaluated.filter(_.status == Failed)
    Option.when(disagree.nonEmpty)(Judged(CheckStatus.Failed, evaluated,
      s"Lean and Scala disagree on ${disagree.size} example(s) or probe(s): the Lean translation does not mean what the Scala does, " +
        s"so nothing proven of ${n.id} is about the code" :: disagree.map(_.detail)))

  /** Proven when Lean reports no error and no `sorry` in it; an authored one states exactly its obligation, with only what a proof file may. */
  def judge(o: ObligationName, e: Elaborated, isAuthored: Boolean): Result =
    val name = o.lean
    e.lean.theorem(name) match
      case None => Result(o, Open, s"no theorem $name in ${e.lean.file}")
      case Some(d) if d.statement != s"Obl.$name" => Result(o, Failed, s"must state exactly Obl.$name")
      case Some(_) if isAuthored && ruled(e.lean.source, "a proof file").isDefined => Result(o, Failed, ruled(e.lean.source, "a proof file").mkString)
      case Some(_) => e.verdict(o) match
        case TheoremVerdict.Proven if e.run.ok => Result(o, Proven, if isAuthored then "authored" else "auto")
        case TheoremVerdict.Proven => Result(o, Open, "not checked: " + clip(e.run.output))
        case v => Result(o, Open, clip(v.why(name).getOrElse("")))

  /** Automation gave up on `complete`: what to do next, and the goal its first steps leave. */
  def gaveUp(g: Generate, n: Node[?], r: Result, state: Option[String]): Result =
    r.copy(detail = s"automation gave up: write theorem complete : Obl.complete in ${proofPath(g, n)} (run `scaffold ${n.id}`)\n" +
      state.fold(s"Lean: ${r.detail}")(ProofState.text(Complete, _)))

  /** What an authored `impl` holds that it may not: it states exactly its obligation, and uses only what a proof file may. */
  def implRules(proof: String): Option[Result] =
    ruled(proof, "a proof file").map(Result(Impl, Failed, _))
      .orElse(Option.when(!LeanSource.theorems(proof).find(_.name == Impl.lean).map(_.statement).contains("Obl.impl"))(
        Result(Impl, Failed, "must state exactly Obl.impl")))

  /** From what the contracts it calls promise, with the axioms its build rests on (none unless proven); else what to do next. */
  def impl(g: Generate, n: Node[?], authored: Boolean, run: Run, state: Option[String]): (Result, Option[List[String]]) =
    val how = if authored then "authored" else "auto"
    val axioms = LeanOutput.axioms(run.output).collectFirst { case (t, as) if t.endsWith("Impl.impl") => as }
    if run.ok && !axioms.exists(_.contains("sorryAx")) then (Result(Impl, Proven, how), axioms)
    else if run.ok then (Result(Impl, Open, "uses sorry"), Some(Nil))
    else (Result(Impl, Open, s"not proven ($how): prove theorem impl : Obl.impl in ${proofPath(g, n)} (run `scaffold ${n.id}`)\n" +
      state.fold("Lean: " + quoted(run))(ProofState.text(Impl, _))), Some(Nil))

  /** The obligations judged: failed, open, or waiting for the parts (a node is proven with its parts). */
  def obligations(g: Generate, n: Node[?], split: List[Result], results: List[Result], parts: List[(String, Option[CheckStatus])]): Option[Judged] =
    val notYet = parts.filterNot(_._2.contains(CheckStatus.Proven))
    if results.exists(_.status == Failed) then Some(Judged(CheckStatus.Failed, results, Nil))
    else if split.exists(_.status == Open) then Some(Judged(CheckStatus.Open, results, Nil, hint = Some(scaffold(g, n))))
    else Option.when(notYet.nonEmpty)(Judged(CheckStatus.Waiting, results, List(s"waiting for its parts: ${notYet.map(_._1).mkString(", ")}")))

  def theorems(results: List[Result], run: Run): Option[Judged] = run match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, results, List("Lean timed out building the node's theorems: run check again")))
    case r if !r.ok => Some(Judged(CheckStatus.Failed, results, "the node's theorems do not build" :: errors(r)))
    case _ => None

  /** The proof file, when it proves obligations of the Checks file: whether to build it, or why it may not be. */
  def proofFile(g: Generate, n: Node[?], proof: String): Either[String, Boolean] =
    if !g.extraObligations(n).exists(o => g.isAuthored(n, o.name)) then Right(false)
    else ruled(proof, proofPath(g, n)).toLeft(true)

  def proofFileBuilt(g: Generate, n: Node[?], run: Run): Option[String] =
    Option.when(!run.ok)(s"${proofPath(g, n)} does not build: " + errors(run).take(5).map(clip(_)).mkString("\n"))

  /** Everything else imports the proof file: what it proves fails, by name, and the file is the message. */
  def proofFileFails(g: Generate, n: Node[?], results: List[Result], why: String): Judged =
    Judged(CheckStatus.Failed, results ++ g.extraObligations(n).filter(o => g.isAuthored(n, o.name)).map(o => Result(o.name, Failed, why)), List(why))

  def checksRan(results: List[Result], run: Run): Option[Judged] = run match
    case Run.TimedOut(_) => Some(Judged(CheckStatus.Timeout, results, List("Lean timed out checking the node (the machine may be busy): run check again")))
    case _ => None

  /** The verdict from the Checks file (one run of Lean) and `root_impl`: each theorem holds with no error, no `sorry`, and its axioms. */
  def finish(a: Analysis, n: Node[?], results: List[Result], impl: Option[(Result, Option[List[String]])], checks: Elaborated,
      root: Option[Either[String, Elaborated]]): Judged =
    val g = a.generate
    // The tries: what Lean proves of them says the node or its split says nothing, or too much.
    val tried = g.tries(n).map(t => (t, checks.verdict(t.obligation.name).proven))
    val fatal = tried.collect { case (t, true) if t.kind.fatal => t.means }
    // Each in plain words: what Lean proved, or that it found no proof within the try's budget (see `TryKind`).
    lazy val idle = g.idleWhat(n)
    val one = g.splitParts(n).collect { case List(c) => c.id }.getOrElse("")
    val tries = tried.map { (t, proven) =>
      Result(t.obligation.name, if proven then Shown else NotShown,
        if !proven then t.kind.unshown(n.id, one, idle) else if t.kind == TryKind.Idle then idle else t.means)
    }
    val extra = g.extraObligations(n).map { o =>
      val how = if g.isAuthored(n, o.name) then "authored" else "auto"
      val vacuous = o.name match
        case ObligationName.Expect(i) => tried.exists((t, p) => p && t.kind == TryKind.VacuousExpect(i))
        case _ => false
      if vacuous then (Result(o.name, Failed, "it holds whatever the node says: it checks nothing"), Some(Nil))
      else checks.verdict(o.name) match
        case TheoremVerdict.Proven => (Result(o.name, Proven, how), checks.axiomsOf(o.name))
        case TheoremVerdict.UsesSorry => (Result(o.name, Open, "uses sorry"), Some(Nil))
        case v => (Result(o.name, Open, s"not proven ($how): prove theorem ${o.name} : Obl.${o.name} in ${proofPath(g, n)}\n" +
          s"Lean: ${clip(v.why(o.name.lean).getOrElse(""))}"), Some(Nil))
    }
    // A view whose coverage cannot be stated keeps nothing proven.
    val uncovered = g.formalKeeps(n).flatMap((i, _) => g.coverage(n, i).left.toOption.map(w =>
      Result(ObligationName.Cover(i.id), Failed, s"what the view must list cannot be stated: $w")))
    val (rootImpl, rootAxioms) = root.map(rootVerdict(g, _)).unzip
    // None when Lean did not report the axioms of a theorem of the Checks file proven: its audit did not finish.
    val audited = (checks.lean.axiomsOf(LeanText.Holds) :: extra.map(_._2) ++ impl.filter(_._1.status == Proven).map(_._2).toList ++
      rootAxioms.toList).sequence.map(_.flatten.distinct.sorted)
    val all = results ++ extra.map(_._1) ++ uncovered ++ tries ++ rootImpl
    audited match
      case _ if fatal.nonEmpty => Judged(CheckStatus.Failed, all, fatal, audited.getOrElse(Nil))
      case None =>
        Judged(CheckStatus.Failed, all, List(s"Lean did not finish checking lean/${checks.lean.file}: ${quoted(checks.run)}"))
      case Some(used) if used.exists(a => !ProofRules.allowedAxioms(a)) =>
        Judged(CheckStatus.Failed, all, List(s"disallowed axioms: ${used.filterNot(ProofRules.allowedAxioms).mkString(", ")}"), used)
      // (What is left open is in the results, once: not repeated as messages.)
      case Some(used) => Judged(CheckStatus.Proven, all, Nil, used)

  /** The root, of the code, from what is trusted only: proven with the axioms Lean printed for it (none printed, it did not finish). */
  private def rootVerdict(g: Generate, root: Either[String, Elaborated]): (Result, Option[List[String]]) =
    def notProven(why: String) = (Result(RootImpl, Open, s"the root is not proven of the code: $why"), Some(Nil))
    // A module that is missing, by name: not the path Lake keeps it at.
    def named(why: String) = MissingModule.replaceAllIn(why, m => scala.util.matching.Regex.quoteReplacement(s"${m.group(1)} did not build"))
    root.fold(notProven, e => (e.verdict(RootImpl), e.axiomsOf(RootImpl)) match
      case (TheoremVerdict.Proven, Some(axioms)) =>
        val trusting = if g.trusted.isEmpty then "nothing" else g.trusted.map(_.id).mkString(", ")
        (Result(RootImpl, Proven, s"the root holds of the code, trusting $trusting"), Some(axioms))
      case (TheoremVerdict.Proven, None) => notProven(s"Lean did not print its axioms: ${quoted(e.run)}")
      case (v, _) => notProven(named(clip(v.why(RootImpl.lean).getOrElse(""), 5000))))
  private val MissingModule = """object file '[^']*' of module (\S+) does not exist""".r

  /** The nodes whose proofs of the code `root_impl` composes: the `Impl` modules RootImpl imports. */
  def composed(kb: KnowledgeBase, g: Generate, rootImpl: String): List[Node[?]] =
    val imports = """(?m)^import\s+(\S+)""".r.findAllMatchIn(rootImpl).map(_.group(1)).toSet
    kb.nodes.filter(c => imports(g.layout.impl(c.id).name))

  /** Whether the proofs of the code it composes built; if not, which did not, as Lake lists the targets that failed. */
  def composedBuilt(g: Generate, composed: List[Node[?]], run: Run): Option[String] =
    def failed(c: Node[?]) =
      val (modules, files) = (Set(g.layout.impl(c.id), g.layout.proofs(c.id)).map(_.name), List(g.layout.impl(c.id).path, g.layout.proofs(c.id).path))
      run.output.linesIterator.exists(l => (l.startsWith("✖") || l.startsWith("- ")) && l.split("\\s+").exists(modules)) ||
        LeanOutput.diagnostics(run.output).exists(d => d.isError && files.exists(d.file.endsWith))
    run match
      case Run.TimedOut(_) => Some("Lean timed out building the proofs of the code it composes: run check again")
      case r if r.ok => None
      case _ => Some(composed.filter(failed).map(_.id) match
        case Nil => s"the proofs of the code it composes do not build: ${quoted(run)}"
        case List(id) => s"$id's impl did not build (check $id says why)"
        case ids => s"the impls of ${ids.mkString(", ")} did not build (check each says why)")
