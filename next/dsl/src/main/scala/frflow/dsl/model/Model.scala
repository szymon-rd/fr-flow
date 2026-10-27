package frflow.dsl.model

import frflow.core.name.ModelName
import frflow.dsl.flow.Recorded
import frflow.dsl.term.{LeanType, Term}

/** The state of a boundary's model, as its model's program reads and writes it: a model is an instance of the
  * boundary's trait over `Model`'s effect, `def database[F[_]: Flow](s: Model[F, CrmStore]): Database[F, Term]`.
  */
trait Model[F[_], S]:
  def get: F[Term[S]]
  def set(s: Term[S]): F[Unit]

object Model:
  /** The state recorded: Lean's `get` and `set` in the model's `StateM`. */
  def recorded[S: LeanType](name: ModelName): Model[Recorded, S] = new Model[Recorded, S]:
    def get: Recorded[Term[S]] = Recorded.Read(name, LeanType[S])
    def set(s: Term[S]): Recorded[Unit] = Recorded.Write(name, s)
