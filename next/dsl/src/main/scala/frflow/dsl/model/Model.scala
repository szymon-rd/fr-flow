package frflow.dsl.model

import frflow.core.name.ModelName
import frflow.dsl.flow.Flow
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.run.Recorded

/** A model's state, as the meaning of an operation on it reads and writes it (`state.get`, `state.set(…)`,
  * `state.update(…)`, in a `StateModel`'s body): Lean's `get` and `set` in the model's `StateM`.
  */
final class Model[S: LeanType](name: ModelName):
  def get: Flow[S] = Flow(Recorded.Read(name, LeanType[S]))
  def set(s: Term[S]): Flow[Unit] = Flow(Recorded.Write(name, s))
  /** The state replaced by `f` of it: its `get`, then its `set`. */
  def update(f: Term[S] => Term[S]): Flow[Unit] = get.flatMap(s => set(f(s)))
