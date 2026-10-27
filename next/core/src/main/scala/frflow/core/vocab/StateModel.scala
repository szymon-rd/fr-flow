package frflow.core.vocab

import frflow.core.name.{BoundaryName, ModelName}
import frflow.core.ty.Ty

/** A boundary's behaviour as a state machine over `state`: each operation's steps on it. Deterministic, never failing
  * on its own, the flow's alone during a run.
  */
final case class StateModel(name: ModelName, boundary: BoundaryName, state: Ty, ops: List[ModelOp])
