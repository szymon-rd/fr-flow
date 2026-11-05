package frflow.core.expr

import frflow.core.name.{ModelName, SymbolName}
import frflow.core.ty.Ty

/** A flow's steps, first order: the free monad over the operations on a state and the models' state, with errors and
  * loops: what the recording of a program gives (`dsl.flow.Recording`). `E` is what a step computes with: the terms
  * themselves (`Stated`, what Lean prints and Scala runs) or their IR (`Expr`, what the analyses read, by
  * `Progs.map`). Concurrent steps hold their branches; their sequential reading is `Progs.sequential`.
  */
enum Prog[+E]:
  case Pure(result: E)
  /** An operation on a state applied (`inRoom(room)`): its Definition, given its meaning by a model
    * (`Vocabulary.modelOf`), or the scheduler's choice of a race's winner (`Prog.leftWins`).
    */
  case Call(op: SymbolName, args: List[E], ty: Ty)
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
    * as `reading`: the scheduler's choice of the winner (a call of `Prog.leftWins`), the loser's steps until it is
    * cancelled (`Cut`), then the winner's. */
  case Race(left: Prog[E], right: Prog[E], reading: Prog[E])
  /** A race's loser until it is cancelled: before each of its steps (an operation's call, a transaction) the
    * scheduler says whether it is cancelled there (`Prog.leftWins` again: `true`, it is, as when the world says
    * nothing); once it is, the rest is dropped, what its steps so far did kept. Gives the unit; an error it raises
    * before it is cancelled is raised (it finished first). */
  case Cut(body: Prog[E])
  /** `finalizer` after `body`, whether it gave a result or failed with an error of type `error`; read as `reading`
    * (the finalizer after a result, and before the error is raised again). */
  case Guard(body: Prog[E], error: Ty, finalizer: Prog[E], reading: Prog[E])
  case ParEach(over: E, x: Binder, body: Prog[E], limit: Option[Int])
  case Atomic(body: Prog[E])

object Prog:
  /** The scheduler's choice of a race's winner (`true`: the left), and of whether a loser is cancelled before its
    * next step (`true`: it is), read from the world's `races`; no model gives it, and no Definition can be named so.
    */
  val leftWins: SymbolName = SymbolName("races.leftWins")
  /** A wait's end at once with others, as Lean reads it (`Waits`): the clock reaches at least the time the sides
    * started at plus the wait's seconds, `reach(start, seconds)`; no Definition can be named so.
    */
  val reach: SymbolName = SymbolName("clock.reach")

  /** How a program's terms pair two step results: what `Progs.sequential` reads a concurrent pair as. */
  trait Pairs[E]:
    def pair(a: Binder, b: Binder): E

  object Pairs:
    given Pairs[Expr] = (a, b) => Expr.Tuple(List(Expr.Var(a), Expr.Var(b)))

  /** How a program's terms name a variable bound by a step: what `Waits` reads a wait's start as. */
  trait Vars[E]:
    def variable(x: Binder): E

  object Vars:
    given Vars[Expr] = x => Expr.Var(x)
