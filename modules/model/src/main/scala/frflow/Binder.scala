package frflow

/** A variable bound by a lambda: `hint` is the name the Scala lambda gave it (`_$1` for a wildcard). */
private[frflow] final class Binder(val hint: String, val tpe: LeanType[?]):
  /** `_` in a lambda, or `_ <-` in a for-comprehension (Scala names it `x$1`). */
  def wildcard: Boolean = hint.startsWith("_$") || hint.matches("x\\$\\d+")
  def term[A]: Term[A] = Term(Tree.Var(this), tpe.asInstanceOf[LeanType[A]])
