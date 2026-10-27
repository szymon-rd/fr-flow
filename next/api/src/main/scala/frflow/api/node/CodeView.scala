package frflow.api.node

import frflow.api.node.tests.TestView
import frflow.core.checking.Shown

/** How a node's code is shown to meet it, piece by piece (`Shown`), and what testing found while current. */
final case class CodeView(shown: Shown, tests: Option[TestView])
