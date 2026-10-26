package frflow.core.name

/** A bound variable's identity, unique in a knowledge base: given by elaboration when it calls a lambda on fresh
  * variables. Two binders are the same variable exactly when their ids are equal (never by object identity).
  */
opaque type VarId = Int

object VarId:
  def apply(i: Int): VarId = i
  extension (v: VarId)
    def value: Int = v
    def next: VarId = v + 1
  given Ordering[VarId] = Ordering.Int
