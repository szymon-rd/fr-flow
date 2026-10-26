package frflow.testing

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.eval.Denote

/** Plain code tested against its contract, with cases seeded by the examples. Pure given a seed. */
object PropertyTests:
  def of(r: Resolved, denote: Denote, node: NodeId, plan: Plan): Option[TestReport] = ???
