package frflow.api.node

import frflow.core.checking.Shown
import frflow.testing.report.TestReport

/** How a node's code is shown to meet it, piece by piece (`Shown`), and what testing found. */
final case class CodeView(shown: Shown, report: Option[TestReport])
