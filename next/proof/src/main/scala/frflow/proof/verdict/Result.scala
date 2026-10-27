package frflow.proof.verdict

import frflow.proof.obligation.ObligationName
import frflow.proof.reading.Diagnostic

/** One obligation's outcome, with Lean's messages about it. */
final case class Result(name: ObligationName, status: ObligationStatus, messages: List[Diagnostic])
