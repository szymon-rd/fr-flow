package frflow.project.program

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.eval.Denote
import frflow.proof.obligation.Evaluation

/** Each contract's examples and probes as Scala evaluates them: the post on the call (and the proven code on the
  * inputs), reflected to `Value`s. Pure: posts and proven code are expressions of the IR.
  */
object Evaluations:
  def of(r: Resolved, denote: Denote): Map[NodeId, List[Evaluation]] = ???
