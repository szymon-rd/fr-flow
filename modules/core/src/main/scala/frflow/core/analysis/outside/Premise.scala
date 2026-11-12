package frflow.core.analysis.outside

import frflow.core.ty.Ty

/** What about the outside a check rests on, by what it must say (owner §16, §21). */
enum Premise:
  /** What values of `ty` from outside meet (an entry Definition's inputs, and values provided where the code runs:
    * what no covered code makes): said by an assumption of `always` on `ty`.
    */
  case FromOutside(ty: Ty)
