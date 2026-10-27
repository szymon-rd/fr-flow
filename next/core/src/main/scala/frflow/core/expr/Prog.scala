package frflow.core.expr

import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.ty.Ty

/** A flow's steps, first order: the free monad over the boundaries' operations and the models' state, with errors and
  * loops: what the recording of a program gives (`dsl.flow.Recording`). `E` is what a step computes with: the terms
  * themselves (`Stated`, what Lean prints and Scala runs) or their IR (`Expr`, what the analyses read, by
  * `Progs.map`). Concurrent steps hold their branches; their sequential reading is `Progs.sequential`.
  */
enum Prog[+E]:
  case Pure(result: E)
  case Call(boundary: BoundaryName, op: OpName, args: List[E], ty: Ty)
  case Bind(first: Prog[E], x: Binder, rest: Prog[E])
  case Let(x: Binder, value: E, rest: Prog[E])
  case Loop(over: E, x: Binder, body: Prog[E])
  case Collect(over: E, x: Binder, body: Prog[E])
  case Accumulate(over: E, init: E, acc: Binder, x: Binder, body: Prog[E])
  case Branch(cond: E, ifTrue: Prog[E], ifFalse: Prog[E])
  case Read(model: ModelName)
  case Write(model: ModelName, state: E)
  case Modify(model: ModelName, x: Binder, next: E)
  case Raise(error: E)
  case Catch(body: Prog[E], error: Ty, x: Binder, handler: Prog[E])
  case Par(left: Prog[E], leftResult: Binder, right: Prog[E], rightResult: Binder)
  /** The first of two to finish gives the result (`Left` or `Right`), the other cancelled; read one step at a time
    * as `reading` (the scheduler's choice of the winner, a call of the `Races` boundary). */
  case Race(left: Prog[E], right: Prog[E], reading: Prog[E])
  /** `finalizer` after `body`, whether it gave a result or failed with an error of type `error`; read as `reading`
    * (the finalizer after a result, and before the error is raised again). */
  case Guard(body: Prog[E], error: Ty, finalizer: Prog[E], reading: Prog[E])
  case ParEach(over: E, x: Binder, body: Prog[E], limit: Option[Int])
  case Atomic(body: Prog[E])

object Prog:
  /** How a program's terms pair two step results: what `Progs.sequential` reads a concurrent pair as. */
  trait Pairs[E]:
    def pair(a: Binder, b: Binder): E

  object Pairs:
    given Pairs[Expr] = (a, b) => Expr.Tuple(List(Expr.Var(a), Expr.Var(b)))
