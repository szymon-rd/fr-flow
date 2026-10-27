package frflow.project.pipeline

import frflow.core.consistency.Vacuity
import frflow.core.example.Example
import frflow.eval.run.OnCode
import frflow.proof.obligation.Constant

/** What running Scala gave, computed by `program.RunScala` before the pure phases: each example against the code,
  * and the witnesses the search found for what must be shown possible.
  */
final case class Computed(examples: List[(Example, OnCode)], found: Map[Vacuity, List[Constant]])

object Computed:
  val none: Computed = Computed(Nil, Map.empty)
