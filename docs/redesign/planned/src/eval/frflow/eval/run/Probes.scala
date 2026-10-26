package frflow.eval.run

import frflow.core.analysis.Resolved
import frflow.core.expr.Value
import frflow.core.name.NodeId
import frflow.eval.*

/** The inputs near a contract's examples that Lean evaluates too (each example with one value moved): deterministic. */
object Probes:
  val Count: Int = 6
  def of(r: Resolved, node: NodeId): List[List[Value]] = ???
