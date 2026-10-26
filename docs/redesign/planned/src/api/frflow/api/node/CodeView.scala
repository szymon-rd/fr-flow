package frflow.api.node

import frflow.core.analysis.Shown
import frflow.core.code.RunCheck
import frflow.testing.TestReport

/** How a node's code is shown to meet it, piece by piece (`Shown`), the run-time check the developer chose, and what
  * testing found.
  */
final case class CodeView(shown: Shown, runCheck: Option[RunCheck], report: Option[TestReport])
