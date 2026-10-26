package frflow.dsl.flow

import frflow.core.name.{BoundaryName, OpName}
import frflow.core.vocab.OpSig
import frflow.dsl.term.Term

/** A boundary bound to its production implementation: a call of one of its operations gives the implementation's flow.
  */
final case class Bound(boundary: BoundaryName, ops: List[OpSig], call: (OpName, List[Term[Any]]) => Flow[Any])
