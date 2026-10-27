package frflow.core.vocab

import frflow.core.expr.{Binder, Prog}
import frflow.core.name.OpName
import frflow.core.term.Stated

/** What a state model does on one operation: its steps over the model's state, from the operation's parameters. */
final case class ModelOp(op: OpName, params: List[Binder], steps: Prog[Stated[?]])
