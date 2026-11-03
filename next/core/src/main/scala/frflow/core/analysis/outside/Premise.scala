package frflow.core.analysis.outside

import frflow.core.name.{ModelName, NodeId}
import frflow.core.ty.Ty

/** What about the outside a check rests on, by what it must say (owner §16, §17, §21, §36). */
enum Premise:
  case OnlyCodeChanges(model: ModelName)
  case Atomic(model: ModelName)
  case Initially(model: ModelName)
  /** Where the world moves the clock's time: the schedule `by` says (owner §47), which Lean's clock takes. */
  case Schedule(model: ModelName, by: NodeId)
  /** What values of `ty` from outside meet (an entry Definition's inputs, and values provided where the code runs:
    * what no covered code makes): said by an assumption of `always` on `ty`.
    */
  case FromOutside(ty: Ty)
