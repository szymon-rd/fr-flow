package frflow.core.vocab

import frflow.core.name.OpName
import frflow.core.ty.Ty

/** One operation of a boundary's trait: its parameters (named as the trait names them) and its result. */
final case class OpSig(name: OpName, params: List[(String, Ty)], result: Ty)
