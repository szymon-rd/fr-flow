package frflow.core.vocab

import frflow.core.expr.{Binder, Prog}
import frflow.core.name.SymbolName
import frflow.core.term.Stated
import frflow.core.ty.Ty

/** What an operation on a state means (`op.means(…)`): its steps over the model's state, from the operation's
  * parameters, and its result's type. `op` is the operation's Definition.
  */
final case class ModelOp(op: SymbolName, params: List[Binder], result: Ty, steps: Prog[Stated[?]]):
  def sig: OpSig = OpSig(op, params.map(p => p.hint -> p.ty), result)
