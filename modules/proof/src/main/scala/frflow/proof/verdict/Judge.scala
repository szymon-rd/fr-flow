package frflow.proof.verdict

import cats.data.NonEmptyList
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.obligation.{Discharge, Obligation, ObligationName}
import frflow.proof.reading.{Elaboration, LeanOutput, ProofFile, ProofRules, TheoremVerdict}

/** The judges of a node's check: each reads what Lean gave at one step, running nothing, and says whether the check
  * ends there (`Option[Judged]`), or what one obligation came to (`Result`); `node` ends a check that got through.
  */
object Judge:
  def model(spec: ProverRun): Option[Judged] = spec match
    case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.LeanTimedOut)))
    case ProverRun.Failed(out) =>
      Some(Judged(CheckStatus.ModelError, Nil, List(Finding.ModelDoesNotBuild(errors(out)))))
    case ProverRun.Built(_)    => None

  /** The shared lemmas: what a proof file may contain, importing no lemmas, built without `sorry`. A lemma that does
    * not build leaves the node importing them not proven (open), not failed: the error is the shared file's, and
    * nothing of the node's own was refuted.
    */
  def lemmas(file: ProofFile, run: ProverRun): Option[Judged] =
    NonEmptyList.fromList(ProofRules.notAllowedInLemmas(file)).map(bad => failed(Finding.ProofNotAllowed(bad.toList)))
      .orElse(run match
        case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.LeanTimedOut)))
        case ProverRun.Failed(out) => Some(Judged(CheckStatus.Open, Nil, List(Finding.LemmasDoNotBuild(errors(out)))))
        case ProverRun.Built(out)  =>
          Option.when(LeanOutput.usesSorry(out))(Judged(CheckStatus.Open, Nil, List(Finding.LemmasDoNotBuild(Nil)))))

  /** A node's proof file: only what one may contain. */
  def proofFile(file: ProofFile): Option[Judged] =
    NonEmptyList.fromList(ProofRules.notAllowed(file)).map(bad => failed(Finding.ProofNotAllowed(bad.toList)))

  /** What must hold (`complete`, `impl`, `cover_<op>`, `commute_i`, …): proven when its theorem states exactly
    * `Obl.<name>` and Lean reports no error and no `sorry` in it; failed when it states anything else.
    */
  def required(o: ObligationName, e: Elaboration): Result =
    val name = LowerObligation.name(o).text
    e.theorems.find(_.name == name) match
      case None                                      => Result(o, ObligationStatus.Open, Nil)
      case Some(t) if t.statement != s"Obl.$name"    => Result(o, ObligationStatus.Failed, Nil)
      case Some(_)                                   => e.verdict(name) match
        case TheoremVerdict.Proven         => Result(o, ObligationStatus.Proven, Nil)
        case TheoremVerdict.Failed(errors) => Result(o, ObligationStatus.Open, errors)
        case _                             => Result(o, ObligationStatus.Open, Nil)

  /** A try (`needed_C`, `vacuous`, `clash`, …) or an example against the claims: shown when Lean proves it within its
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
      case ObligationName.Tried(_) | ObligationName.Example(_) => false
      case _                                                    => true)
    if fatal.nonEmpty then Judged(CheckStatus.Failed, results, List(Finding.Refuted(fatal)))
    else if disallowed.nonEmpty then Judged(CheckStatus.Failed, results, List(Finding.DisallowedAxioms(disallowed)))
    else if required.exists(_.status == ObligationStatus.Failed) then Judged(CheckStatus.Failed, results, Nil)
    else if required.exists(_.status != ObligationStatus.Proven) then Judged(CheckStatus.Open, results, Nil)
    else if parts.exists(_ != CheckStatus.Proven) then Judged(CheckStatus.Waiting, results, Nil)
    else Judged(CheckStatus.Proven, results, Nil)

  private def failed(f: Finding): Judged = Judged(CheckStatus.Failed, Nil, List(f))
  private def errors(out: String) = LeanOutput.diagnostics(out).filter(_.error)
