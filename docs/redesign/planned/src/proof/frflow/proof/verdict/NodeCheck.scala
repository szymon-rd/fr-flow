package frflow.proof.verdict

import frflow.core.name.NodeId
import java.time.Instant

/** A node's check as recorded (`.frflow/checks.json`). Current while its key is the node's key now. */
final case class NodeCheck(node: NodeId, key: CheckKey, status: CheckStatus, results: List[Result],
    findings: List[Finding], at: Instant)
