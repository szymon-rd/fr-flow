package frflow.core.vocab

import frflow.core.name.{ModelName, SymbolName}
import frflow.core.ty.Ty

/** The meaning of the operations on one state (owner §36): each operation's steps on `state`, a field of the World,
  * in the order the meanings are given, and what a call fails with when the operations may fail. Deterministic, the
  * flow's alone during a run. Each operation is a Definition; its plain Scala is given apart (`code.Implementation`).
  */
final case class StateModel(name: ModelName, means: String, state: Ty, ops: List[ModelOp], fails: Option[Fails]):
  def failsWith: Option[Ty] = fails.map(_.ty)
  def op(s: SymbolName): Option[ModelOp] = ops.find(_.op == s)
  def sigs: List[OpSig] = ops.map(_.sig)
