package frflow.dsl.model

import frflow.core.name.ModelName
import frflow.core.term.{Sym, World}
import frflow.dsl.build.Source
import frflow.dsl.flow.Recorded
import frflow.dsl.term.{LeanType, Notes, Term}

/** A model's state, named as its val: what a world holds of it, read in a claim as `stored.in(before)`. A
  * boundary's model is declared with its instance (`store.model(…)(Stored(_))`, a `StoreModel`); a state alone,
  * `ModelState[Tables]("the database's tables")`, is one whose model is written in Lean.
  */
final class ModelState[S](val name: ModelName, val means: String)(using val leanType: LeanType[S]):
  /** The state as a model's recorded steps read and write it. */
  def recorded: Model[Recorded, S] = Model.recorded(name)
  /** What `world` holds of it. */
  def in(world: Term[World]): Term[S] =
    Term.noted(Notes.of(leanType.declares))([T[_]] => (s: Sym[T]) => s.part[S](world.run(s), name, leanType.ty))

object ModelState:
  inline def apply[S: LeanType](means: String): ModelState[S] = new ModelState[S](ModelName(Source.valName), means)
