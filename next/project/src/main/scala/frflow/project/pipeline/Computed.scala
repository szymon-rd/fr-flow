package frflow.project.pipeline

import frflow.core.consistency.Vacuity
import frflow.core.example.Example
import frflow.core.name.NodeId
import frflow.eval.run.OnCode
import frflow.proof.obligation.Constant
import frflow.testing.search.Refuted

/** What running Scala gave, computed by `program.RunScala` before the pure phases: each example against the code,
  * the witnesses the search found for what must be shown possible, and, for each node with one part fixing a
  * Definition's answer, a case refuting its step should Lean not prove it.
  */
final case class Computed(examples: List[(Example, OnCode)], found: Map[Vacuity, List[Constant]],
    refutations: Map[NodeId, Refuted])

object Computed:
  val none: Computed = Computed(Nil, Map.empty, Map.empty)
