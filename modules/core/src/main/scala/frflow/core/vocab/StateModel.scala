package frflow.core.vocab

import frflow.core.name.{ModelName, SymbolName}
import frflow.core.ty.Ty

/** The meaning of the operations on one state (owner §36): each operation's steps on `state`, a field of the World,
  * in the order the meanings are given, and what a call fails with when the operations may fail. Deterministic, the
  * flow's alone during a run. Each operation is a Definition; its plain Scala is given apart (`code.Implementation`).
  * An operation given no steps (`assumed`, G2) is known only by the assumptions about it: on its field of the World it
  * may give any result and leave any state, but what those say (owner §36, "the assumed case"). The clock (`timed`)
  * is one model, FrFlow's own (owner §47).
  */
final case class StateModel(name: ModelName, means: String, state: Ty, ops: List[ModelOp], fails: Option[Fails],
    assumed: List[OpSig] = Nil, timed: Option[Timed] = None):
  def failsWith: Option[Ty] = fails.map(_.ty)
  /** An operation's meaning, of one given steps. */
  def op(s: SymbolName): Option[ModelOp] = ops.find(_.op == s)
  /** The signatures of the operations given steps: the methods of the model's class in Lean. */
  def sigs: List[OpSig] = ops.map(_.sig)
  /** Every operation's signature: those given steps, then those known only by assumptions. */
  def allSigs: List[OpSig] = sigs ++ assumed
  def sigOf(s: SymbolName): Option[OpSig] = allSigs.find(_.name == s)
  /** Every operation, those given steps first. */
  def operations: List[SymbolName] = allSigs.map(_.name)
  /** Whether `s` is an operation of this model known only by assumptions. */
  def isAssumed(s: SymbolName): Boolean = assumed.exists(_.name == s)
  /** The steps the world takes on this state between runs, never called by code: the clock's `elapse`. */
  def outside: List[SymbolName] = timed.map(_.elapse).toList
