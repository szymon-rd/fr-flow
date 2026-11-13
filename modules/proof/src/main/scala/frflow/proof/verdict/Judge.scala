package frflow.proof.verdict

import cats.data.NonEmptyList
import frflow.proof.prover.lower.LowerObligation
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.{Diagnostic, Elaboration, ProofFile, ProofRules, RocqReport, RocqSource, TheoremVerdict}

/** The judges of a node's check: each reads what the prover gave at one step, running nothing, and says whether the
  * check ends there (`Option[Judged]`), or what one obligation came to (`Result`); `node` ends a check that got
  * through.
  */
object Judge:
  def model(spec: ProverRun): Option[Judged] = spec match
    case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.TimedOut)))
    case ProverRun.Failed(out) =>
      Some(Judged(CheckStatus.ModelError, Nil, List(Finding.ModelDoesNotBuild(errors(out)))))
    case ProverRun.Built(_)    => None

  /** The shared lemmas: what a proof file may contain, importing no lemmas, every one proven. A lemma that is not
    * leaves the node importing them not proven (open), not failed: the error is the shared file's, and nothing of the
    * node's own was refuted.
    */
  def lemmas(file: ProofFile, run: ProverRun): Option[Judged] =
    NonEmptyList.fromList(ProofRules.notAllowedInLemmas(file)).map(bad => failed(Finding.ProofNotAllowed(bad.toList)))
      .orElse(run match
        case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.TimedOut)))
        case ProverRun.Failed(out) => Some(Judged(CheckStatus.Open, Nil, List(Finding.LemmasDoNotBuild(in(file, out)))))
        case ProverRun.Built(out)  => Option.when(errors(out).nonEmpty)(
          Judged(CheckStatus.Open, Nil, List(Finding.LemmasDoNotBuild(in(file, out))))))

  /** What a build's report says is wrong, a lemma of `file` at the line it is stated on. */
  private def in(file: ProofFile, out: String): List[Diagnostic] =
    val at = RocqSource.lemmas(file.source).map(l => s"${l.name}: " -> l.from)
    errors(out).map(d => at.collectFirst { case (name, line) if d.message.startsWith(name) => d.copy(line = line) }
      .getOrElse(d))

  /** A node's proof file: only what one may contain. */
  def proofFile(file: ProofFile): Option[Judged] =
    NonEmptyList.fromList(ProofRules.notAllowed(file)).map(bad => failed(Finding.ProofNotAllowed(bad.toList)))

  /** What must hold (`complete`, `impl`, `made_<maker>`, …): proven when its lemma states exactly the obligation
    * and Rocq accepts its proof; failed when it states anything else.
    */
  def required(o: ObligationName, e: Elaboration): Result =
    val name = LowerObligation.name(o).text
    e.stated(name) match
      case None                                           => Result(o, ObligationStatus.Open, Nil)
      case Some(t) if t.statement != e.obligation(name)   => Result(o, ObligationStatus.Failed, Nil)
      case Some(_)                                        => e.verdict(name) match
        case TheoremVerdict.Proven         => Result(o, ObligationStatus.Proven, Nil)
        case TheoremVerdict.Failed(errors) => Result(o, ObligationStatus.Open, errors)
        case _                             => Result(o, ObligationStatus.Open, Nil)

  /** A try (`needed_C`, `vacuous`, `clash`, …) or an example against the claims: shown when Rocq proves it within its
    * budget, else not shown (one-sided: that says nothing).
    */
  def tried(o: ObligationName, e: Elaboration): Result =
    val shown = e.verdict(LowerObligation.name(o).text) == TheoremVerdict.Proven
    Result(o, if shown then ObligationStatus.Shown else ObligationStatus.NotShown, Nil)

  /** What is asked of the theory as a whole: a statement no witness was found for stays open ("consistency not
    * proven", "not shown"), not failed, until the developer's proof file proves it.
    */
  def whole(o: Obligation, e: Elaboration): Result = o.discharge match
    case Discharge.Attempt(_) => tried(o.name, e)
    case _                    => required(o.name, e)

  /** A check that got through every step: failed when a fatal try is shown, an obligation failed or a proof rests on
    * an axiom not allowed; open when one is not proven; waiting while a part is not proven; else proven.
    */
  def node(results: List[Result], axioms: List[String], parts: List[CheckStatus]): Judged =
    val fatal = results.collect { case Result(ObligationName.Tried(k), ObligationStatus.Shown, _) if k.fatal => k }
    val disallowed = axioms.distinct.filterNot(ProofRules.AllowedAxioms)
    val required = results.filter(_.name match
      case ObligationName.Tried(_) | ObligationName.Example(_, _) | ObligationName.ExampleOpposite(_, _) => false
      case _                                                                                         => true)
    if fatal.nonEmpty then Judged(CheckStatus.Failed, results, List(Finding.Refuted(fatal)))
    else if disallowed.nonEmpty then Judged(CheckStatus.Failed, results, List(Finding.DisallowedAxioms(disallowed)))
    else if required.exists(_.status == ObligationStatus.Failed) then Judged(CheckStatus.Failed, results, Nil)
    else if required.exists(_.status != ObligationStatus.Proven) then Judged(CheckStatus.Open, results, Nil)
    else if parts.exists(_ != CheckStatus.Proven) then Judged(CheckStatus.Waiting, results, Nil)
    else Judged(CheckStatus.Proven, results, Nil)

  private def failed(f: Finding): Judged = Judged(CheckStatus.Failed, Nil, List(f))
  /** What a build's report says is wrong, file by file: a file Rocq could not read, a lemma it did not accept. */
  private def errors(out: String): List[Diagnostic] = RocqReport.read(out).flatMap(f =>
    f.broken.map(Diagnostic(f.path, 0, true, _)).toList ++
      f.open.toList.sortBy(_._1).map((l, m) => Diagnostic(f.path, 0, true, s"$l: $m")))
