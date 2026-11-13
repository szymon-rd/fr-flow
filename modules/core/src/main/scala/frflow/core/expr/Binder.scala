package frflow.core.expr

import frflow.core.name.VarId
import frflow.core.ty.Ty

/** A variable a lambda, a quantifier, a `let` or a pattern binds. `hint` is the name the Scala lambda gave it (`u`,
  * `_$1` for a wildcard): Rocq names it from the hint, made unique by the lowering. Identity is `id`.
  */
final case class Binder(id: VarId, hint: String, ty: Ty):
  def wildcard: Boolean = hint.startsWith("_$") || hint.matches("x\\$\\d+")
