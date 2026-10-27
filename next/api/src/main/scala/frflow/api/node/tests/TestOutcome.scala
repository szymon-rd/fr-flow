package frflow.api.node.tests

import frflow.eval.EvalError

/** What a run of tests found: every case tried passed, one failed (the smallest such case), or the statement has no
  * Scala value to test against ("not checked").
  */
enum TestOutcome:
  case Passed
  case Failed(failure: FailedCase)
  case NotChecked(error: EvalError)
