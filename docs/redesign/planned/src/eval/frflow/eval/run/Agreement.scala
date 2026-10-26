package frflow.eval.run

import frflow.core.example.Verdict
import frflow.core.expr.Value

/** Whether a run agrees with what an example says, and if not, how. */
enum Agreement:
  case Agrees
  case PromiseRefuses, PromiseAccepts
  case Returned(value: Value)
  case Breaks(broken: Broken)

object Agreement:
  /** The promise's answer against the example's verdict. */
  def judged(holds: Boolean, verdict: Verdict): Agreement = (holds, verdict) match
    case (true, Verdict.Expect) | (false, Verdict.Reject) => Agrees
    case (false, Verdict.Expect)                          => PromiseRefuses
    case (true, Verdict.Reject)                           => PromiseAccepts
