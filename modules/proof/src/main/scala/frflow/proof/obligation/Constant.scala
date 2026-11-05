package frflow.proof.obligation

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** A closed value as Lean is given it: a value of a type. */
final case class Constant(value: Value, ty: Ty)
