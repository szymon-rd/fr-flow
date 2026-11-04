package frflow.proof.verdict

import frflow.core.name.NodeId

/** What `.frflow/checks.json` records: each node's check, and the theory's own (none before it is first checked). */
final case class Checks(nodes: Map[NodeId, NodeCheck], whole: Option[WholeCheck])

object Checks:
  val none: Checks = Checks(Map.empty, None)
