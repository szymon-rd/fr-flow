package frflow.runtime

import frflow.core.name.NodeId
import frflow.eval.run.Broken
import frflow.eval.ScalaValue

/** A broken promise where code runs: the contract, what broke (the post, its check, an invariant, an assumption),
  * the call's inputs and its result (none when an assumption broke).
  */
final case class Violation(contract: NodeId, check: Broken, inputs: List[ScalaValue], result: Option[ScalaValue])
