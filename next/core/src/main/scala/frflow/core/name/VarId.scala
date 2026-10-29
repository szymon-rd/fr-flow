package frflow.core.name

/** A bound variable's identity in the IR, given without ambient state or source positions. A term's binder is its
  * de Bruijn level, the number of binders around it, as the IR interpreter counts them while it runs
  * (`term.interpret.ToExpr`, LNCS 7470 §3.2's depth); a recorded program's step is numbered by the reading of the
  * recording (negative, apart from every level). Two binders on one path from a term's root never share a level.
  * A statement being written has three more kinds, each free only until the statement is closed (owner §41): the
  * current world (`world`), a leading variable opened (`opened`), and a run's result or world after (`ran`), all
  * below every step's number.
  */
opaque type VarId = Long

object VarId:
  def level(depth: Int): VarId = depth.toLong
  def step(n: Int): VarId = -1L - n
  /** The world a statement holds in, read in it without being named. */
  val world: VarId = Long.MinValue
  /** The `k`th leading variable of a statement, opened to be read below it. */
  def opened(k: Int): VarId = Long.MinValue + 1 + k
  /** A run's result (`side` 0) or its world after (`side` 1), by the run's key. */
  def ran(key: Int, side: Int): VarId = Long.MinValue + (1L << 40) + (key.toLong & 0xffffffffL) * 2 + side
  /** Whether the variable is a run's result or world after (`ran`). */
  def isRan(v: VarId): Boolean = v >= Long.MinValue + (1L << 40) && v < Long.MinValue + (1L << 41)
  extension (v: VarId) def value: Long = v
  given Ordering[VarId] = Ordering.Long
