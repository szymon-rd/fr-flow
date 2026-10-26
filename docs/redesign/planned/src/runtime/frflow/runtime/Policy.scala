package frflow.runtime

import frflow.core.code.{Attachment, Code, RunCheck}

/** How a contract's code is checked where it runs: as the developer chose, else by whether Lean proves it. */
object Policy:
  def of(a: Attachment): RunCheck = a.runCheck.getOrElse(a.code match
    case Code.Proven(_) => RunCheck.Never
    case _              => RunCheck.EveryCall)
