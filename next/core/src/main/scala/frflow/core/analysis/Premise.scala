package frflow.core.analysis

import frflow.core.name.ModelName
import frflow.core.ty.Ty

/** What about the outside a check rests on, by what it must say (owner §16, §17, §21). */
enum Premise:
  case BehavesAs(model: ModelName)
  case OneRunAtATime(model: ModelName)
  case Initially(model: ModelName)
  case WrittenOnlyBy(model: ModelName)
  /** What values of `ty` from outside meet (an entry Definition's inputs, and values provided where the code runs:
    * what no covered code makes): said by an assumption of `always` on `ty`.
    */
  case FromOutside(ty: Ty)
