package frflow.proof.verdict

import frflow.proof.reading.LeanOutput

/** The judges of a node's check: each reads what Lean gave at one step and says whether the check ends there. */
object Judge:
  def model(spec: ProverRun): Option[Judged] = spec match
    case ProverRun.TimedOut(_) => Some(Judged(CheckStatus.Timeout, Nil, List(Finding.LeanTimedOut)))
    case ProverRun.Failed(out) =>
      Some(Judged(CheckStatus.ModelError, Nil, List(Finding.ModelDoesNotBuild(errors(out)))))
    case ProverRun.Built(_)    => None

  // … lemmas, complete, impl, tries, the theory's consistency and examples: one function each.

  private def errors(out: String) = LeanOutput.diagnostics(out).filter(_.error)
