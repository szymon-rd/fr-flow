package frflow.api

import cats.MonadThrow
import cats.effect.Ref
import frflow.api.shell.ModelTests
import frflow.dsl.model.AdapterCheck

/** A store's implementation, as the project gives it to be tested against its model (`stored.checkedAgainst(…)`,
  * `stored.implementedBy(…)`).
  */
final class Adapter[F[_]] private (private[api] val tests: ModelTests[F])

object Adapter:
  def apply[F[_]: MonadThrow: Ref.Make, B[_[_], _[_]], S, A <: B[F, cats.Id]](check: AdapterCheck[F, B, S, A])
      : Adapter[F] = new Adapter(ModelTests(check))
