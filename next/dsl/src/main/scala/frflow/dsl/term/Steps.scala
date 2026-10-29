package frflow.dsl.term

import frflow.core.term.Program

/** What a program's effect `F` does with an operation on a state applied (`inRoom(request.room)`, a
  * `Term[Program[R]]`): runs it as one step. `flow.Flow` is one; `Term`'s conversions make such a term a step where
  * a step is expected, so a program calls an operation as any Definition (owner §36).
  */
trait Steps[F[_]]:
  /** The operation run, its result a term. */
  def step[R: LeanType](op: Term[Program[R]]): F[Term[R]]
  /** An operation giving nothing, run: the step a program writes where an `F[Unit]` is expected. */
  def run(op: Term[Program[Unit]]): F[Unit]
