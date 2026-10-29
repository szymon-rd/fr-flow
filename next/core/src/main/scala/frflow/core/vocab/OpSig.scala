package frflow.core.vocab

import frflow.core.name.SymbolName
import frflow.core.ty.Ty

/** One operation on a model's state, as its Definition is typed: its parameters (named as its meaning names them)
  * and its result.
  */
final case class OpSig(name: SymbolName, params: List[(String, Ty)], result: Ty)
