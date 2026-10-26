package frflow.api

import cats.effect.{Async, Resource}
import frflow.core.Elaborated

/** FrFlow as a front end sees it. Interpreters: the live one over a project, the in-memory one the front ends test
  * on. */
final case class FrFlowApi[F[_]](reading: Reading[F], deciding: Deciding[F], proving: Proving[F])

object FrFlowApi:
  /** The project at `root`, held for the life of the resource (the ledger's lock, a pool of `lake` processes). */
  def make[F[_]: Async](e: Elaborated, root: java.nio.file.Path): Resource[F, FrFlowApi[F]] = ???
