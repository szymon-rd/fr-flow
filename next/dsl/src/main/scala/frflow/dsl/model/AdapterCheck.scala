package frflow.dsl.model

import cats.Id
import frflow.core.code.Realizes

/** An implementation of a boundary to be checked against its model: how it is made holding a state of the model,
  * how its state is read back, and whose it is (`Realizes`): an outside system's (`stored.checkedAgainst(…)`: a
  * database, its model assumed and checked on fewer runs) or the project's own (`stored.implementedBy(…)`: tested on
  * every run). `testing.model.ModelRuns` runs generated calls on it and on the model, and compares their answers
  * and, at the end, their states.
  */
final case class AdapterCheck[F[_], B[_[_], _[_]], S, A <: B[F, Id]](model: StoreModel[B, S], start: S => F[A],
    observe: A => F[S], realizes: Realizes)
