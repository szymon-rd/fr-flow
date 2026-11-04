package frflow.core.vocab

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** What a call of an operation of a failing model fails with: an error of type `ty`, the value `error` (the store's
  * `StoreUnavailable`), changing nothing.
  */
final case class Fails(ty: Ty, error: Value)
