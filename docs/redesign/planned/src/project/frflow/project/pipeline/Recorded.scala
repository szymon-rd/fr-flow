package frflow.project.pipeline

import frflow.core.name.NodeId
import frflow.proof.verdict.NodeCheck
import frflow.testing.{Failure, TestReport}

/** What earlier runs recorded, reused while current (a check while its key is the node's, a test report while its
  * key is); the failing cases are kept to replay first, and committed.
  */
final case class Recorded(checks: Map[NodeId, NodeCheck], tests: Map[NodeId, (String, TestReport)],
    counterexamples: Map[NodeId, List[Failure]])
