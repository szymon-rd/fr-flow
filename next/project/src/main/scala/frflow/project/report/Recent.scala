package frflow.project.report

import frflow.proof.verdict.NodeCheck
import frflow.testing.report.TestReport

/** What earlier runs recorded of a node and is current: its check (none before Lean is run on it, or since it moved),
  * and its tests' report (none when nothing tests it, or it was not tested since it moved).
  */
final case class Recent(check: Option[NodeCheck], tests: Option[TestReport])
