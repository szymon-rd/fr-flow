package frflow.dsl.model

import cats.Id

/** An implementation of a boundary to be checked against its model (`stored.checkedAgainst(start = …, observe =
  * …)`): how it is made holding a state of the model, and how its state is read back. `testing.ModelTests` runs
  * generated calls on it and on the model, and compares their answers and, at the end, their states.
  */
final case class AdapterCheck[F[_], B[_[_], _[_]], S, A <: B[F, Id]](model: StoreModel[B, S], start: S => F[A],
    observe: A => F[S])
