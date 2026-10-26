package frflow.core.vocab

import frflow.core.name.BoundaryName
import frflow.core.ty.Ty

/** A boundary: the operations proven code calls but cannot see, in the trait's order, and the error a call may fail
  * with. */
final case class BoundarySig(name: BoundaryName, className: String, means: String, ops: List[OpSig],
    failsWith: Option[Ty])
