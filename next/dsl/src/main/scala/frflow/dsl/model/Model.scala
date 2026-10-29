package frflow.dsl.model

import frflow.core.name.ModelName
import frflow.dsl.flow.Recorded
import frflow.dsl.term.{LeanType, Term}

/** A model's state, as the meaning of an operation on it reads and writes it (`state.get`, `state.set(…)`,
  * `state.update(…)`, in a `StateModel`'s body).
  */
trait Model[F[_], S]:
  def get: F[Term[S]]
  def set(s: Term[S]): F[Unit]
  /** The state replaced by `f` of it: its `get`, then its `set`. */
  def update(f: Term[S] => Term[S]): F[Unit]

object Model:
  /** The state recorded: Lean's `get` and `set` in the model's `StateM`. */
  def recorded[S: LeanType](name: ModelName): Model[Recorded, S] = new Model[Recorded, S]:
    def get: Recorded[Term[S]] = Recorded.Read(name, LeanType[S])
    def set(s: Term[S]): Recorded[Unit] = Recorded.Write(name, s)
    def update(f: Term[S] => Term[S]): Recorded[Unit] = Recorded.Bind(get, (s: Term[S]) => set(f(s)))
