package frflow.core.vocab

import frflow.core.name.BoundaryName
import frflow.core.ty.Ty

/** A boundary: the operations proven code calls but cannot see, in the trait's order, and what a call fails with
  * when it may. */
final case class BoundarySig(name: BoundaryName, className: String, means: String, ops: List[OpSig],
    fails: Option[Fails]):
  def failsWith: Option[Ty] = fails.map(_.ty)
