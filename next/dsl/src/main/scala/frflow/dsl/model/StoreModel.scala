package frflow.dsl.model

import cats.Id
import cats.syntax.all.*
import frflow.core.name.ModelName
import frflow.core.term.World
import frflow.core.vocab.StateModel
import frflow.dsl.build.Declarations
import frflow.dsl.flow.{Boundary, Recorded}
import frflow.dsl.term.Term

/** A boundary's model, named as its val (`val stored = store.model("every booking …")(Stored(_))`): its state, read
  * in a world as `stored.in(before)`, and the developer's instance of the boundary's trait over that state, which
  * Lean proves programs on (`Node.assumption(stored)(…)`) and implementations are tested against
  * (`stored.checkedAgainst(…)`).
  */
final class StoreModel[B[_[_], _[_]], S](val state: ModelState[S], val boundary: Boundary[B],
    instance: Model[Recorded, S] => B[Recorded, Term]):
  def name: ModelName = state.name
  def in(world: Term[World]): Term[S] = state.in(world)

  /** The model as the vocabulary holds it: each operation's steps over the state, read from the instance. */
  lazy val stateModel: StateModel =
    StateModel(state.name, boundary.name, state.leanType.ty, boundary.ops.model(instance(state.recorded)))
  def declares: Declarations =
    Declarations.boundary(boundary.sig, stateModel) |+| state.leanType.declares |+| boundary.declares

  /** An implementation checked against the model: `start` makes it hold a state of the model, `observe` reads its
    * state back.
    */
  def checkedAgainst[F[_], A <: B[F, Id]](start: S => F[A], observe: A => F[S]): AdapterCheck[F, B, S, A] =
    AdapterCheck(this, start, observe)
