package frflow.project.pipeline

import frflow.core.name.NodeId
import frflow.eval.run.ExampleResult
import frflow.proof.obligation.Evaluation

/** What running Scala gave, computed by `program.Evaluate` before the pure phases: each node's examples run, and the
  * examples and probes evaluated for Lean to agree with.
  */
final case class Computed(examples: Map[NodeId, List[ExampleResult]], evaluations: Map[NodeId, List[Evaluation]])
