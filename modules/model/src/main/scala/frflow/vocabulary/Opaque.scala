package frflow
package vocabulary

import frflow.types.Shape

/** A domain type, open until a definition fixes it: `val User = Opaque("User", "a person with an account")`, used as `User.T`. */
final class Opaque(val name: String, val means: String):
  type T
  given leanType: LeanType[T] = LeanType.of(Shape.Opq(this))
  def :=(t: LeanType[?]): Subst = Subst(name, this, isType = true, Some(t), None)
