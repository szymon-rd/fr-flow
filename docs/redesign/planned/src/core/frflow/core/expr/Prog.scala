package frflow.core.expr

import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.ty.Ty

/** A flow's steps, first order: the free monad over the boundaries' operations and the models' state, with errors and
  * loops. Concurrent steps hold their branches only; their sequential reading is `Progs.sequential`.
  */
enum Prog:
  case Pure(result: Expr)
  case Call(boundary: BoundaryName, op: OpName, args: List[Expr], ty: Ty)
  case Bind(first: Prog, x: Binder, rest: Prog)
  case Let(x: Binder, value: Expr, rest: Prog)
  case Loop(over: Expr, x: Binder, body: Prog)
  case Collect(over: Expr, x: Binder, body: Prog)
  case Accumulate(over: Expr, init: Expr, acc: Binder, x: Binder, body: Prog)
  case Branch(cond: Expr, ifTrue: Prog, ifFalse: Prog)
  case Read(model: ModelName)
  case Write(model: ModelName, state: Expr)
  case Modify(model: ModelName, x: Binder, next: Expr)
  case Raise(error: Expr)
  case Catch(body: Prog, error: Ty, x: Binder, handler: Prog)
  case Par(left: Prog, leftResult: Binder, right: Prog, rightResult: Binder)
  case ParEach(over: Expr, x: Binder, body: Prog, limit: Option[Int])
  case Atomic(body: Prog)
