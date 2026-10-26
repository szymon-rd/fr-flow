package frflow.core.name

/** A bound variable's identity in the IR, given without ambient state or source positions. A term's binder is its
  * de Bruijn level, the number of binders around it, as the IR interpreter counts them while it runs
  * (`term.interpret.ToExpr`, LNCS 7470 §3.2's depth); a recorded program's step is numbered by the reading of the
  * recording (negative, apart from every level). Two binders on one path from a term's root never share a level.
  */
opaque type VarId = Long

object VarId:
  def level(depth: Int): VarId = depth.toLong
  def step(n: Int): VarId = -1L - n
  extension (v: VarId) def value: Long = v
  given Ordering[VarId] = Ordering.Long
