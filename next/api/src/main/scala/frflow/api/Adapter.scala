package frflow.api

import cats.{Id, MonadThrow}
import cats.effect.Ref
import frflow.dsl.model.AdapterCheck

/** A store's implementation, as the project gives it to be tested against its model (`stored.checkedAgainst(…)`,
  * `stored.implementedBy(…)`): the check, with what running it needs.
  */
sealed trait Adapter[F[_]]:
  type Boundary[_[_], _[_]]
  type State
  type Implementation <: Boundary[F, Id]
  def check: AdapterCheck[F, Boundary, State, Implementation]
  def monad: MonadThrow[F]
  def refs: Ref.Make[F]

object Adapter:
  def apply[F[_], B[_[_], _[_]], S, A <: B[F, Id]](c: AdapterCheck[F, B, S, A])(using m: MonadThrow[F],
      r: Ref.Make[F]): Adapter[F] = new Adapter[F]:
    type Boundary[G[_], T[_]] = B[G, T]
    type State = S
    type Implementation = A
    val check: AdapterCheck[F, Boundary, State, Implementation] = c
    val monad: MonadThrow[F] = m
    val refs: Ref.Make[F] = r
