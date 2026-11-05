package frflow.testing.report

import frflow.eval.EvalError

/** What a run of tests found: every case tried passed, one failed (the smallest such case), or the statement has no
  * Scala value to test against (it quantifies over a type, or reads a value the test is not given): "not checked",
  * which no case is shrunk, saved or replayed for.
  */
enum Outcome:
  case Passed
  case Failed(failure: Failure)
  case NotChecked(error: EvalError)
