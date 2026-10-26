package frflow.project.program

import frflow.core.name.NodeId
import frflow.project.pipeline.Analysis

/** Which nodes a check runs, in levels: every node after its parts and callees, those whose recorded check is
  * current left out (or only `only` and what it needs).
  */
object CheckPlan:
  def levels(a: Analysis, only: Option[NodeId]): List[List[NodeId]] = ???
