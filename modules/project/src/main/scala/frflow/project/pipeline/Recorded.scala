package frflow.project.pipeline

import frflow.core.name.NodeId
import frflow.proof.verdict.Checks
import frflow.testing.report.{Failure, TestReport}

/** What earlier runs recorded, reused while current: each node's check and the theory's own (`checks.json`, current
  * while its key is the one computed now), each node's test report with its key (`tests.json`), and the failing
  * cases kept to replay first (`counterexamples.json`, committed).
  */
final case class Recorded(checks: Checks, tests: Map[NodeId, (String, TestReport)],
    counterexamples: Map[NodeId, List[Failure]])

object Recorded:
  val none: Recorded = Recorded(Checks.none, Map.empty, Map.empty)
