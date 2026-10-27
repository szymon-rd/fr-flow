package frflow.api.shell

import cats.effect.Ref
import cats.{Id, MonadThrow}
import frflow.core.Theory
import frflow.dsl.model.AdapterCheck
import frflow.eval.Semantics
import frflow.project.program.ModelCheck

/** A store's implementation as the shell tests it: the model check, once the model is read. */
private[api] trait ModelTests[F[_]]:
  def of(semantics: Semantics, t: Theory): Option[ModelCheck[F]]

private[api] object ModelTests:
  def apply[F[_]: MonadThrow: Ref.Make, B[_[_], _[_]], S, A <: B[F, Id]](c: AdapterCheck[F, B, S, A])
      : ModelTests[F] = (semantics, t) => ModelCheck.of(c, semantics, t)
