package frflow.proof.verdict

import frflow.proof.reading.LeanOutput

/** The judges of a node's check: each reads what Lean gave at one step and says whether the check ends there. */
object Judge:
  def model(spec: ProverRun): Option[Judged] = spec match
    case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.LeanTimedOut)))
    case ProverRun.Failed(out) =>
      Some(Judged(CheckStatus.ModelError, Nil, List(Finding.ModelDoesNotBuild(errors(out)))))
    case ProverRun.Built(_)    => None

  def waiting(undecided: List[String]): Option[Judged] =
    Option.when(undecided.nonEmpty)(Judged(CheckStatus.Waiting, Nil, List(Finding.WaitsForChoice(undecided))))
  // … lemmas, evaluations (Lean and Scala agree), complete, impl, tries: one function each.

  private def errors(out: String) = LeanOutput.diagnostics(out).filter(_.error)
