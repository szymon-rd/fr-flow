package frflow.eval.run

import cats.effect.kernel.{Async, Sync}
import cats.effect.kernel.implicits.parallelForGenSpawn
import cats.effect.std.Mutex
import cats.Parallel
import cats.syntax.all.*
import frflow.core.name.BoundaryName
import frflow.dsl.flow.Bound
import frflow.eval.Denote

/** A flow run against the bound implementations of its boundaries: in turn (`SyncIO` in examples and tests), or with
  * its branches at once and `atomically` under one lock (`IO` in production, and the interleavings tests).
  */
object FlowRun:
  def sequential[F[_]: Sync](denote: Denote, bound: Map[BoundaryName, Bound]): FlowInterpreter[F] =
    FlowInterpreter(denote, bound, [A] => (fa: F[A]) => fa, Sync[F].unit)(using Sync[F], Parallel.identity[F])

  def concurrent[F[_]: Async](denote: Denote, bound: Map[BoundaryName, Bound], pause: F[Unit])
      : F[FlowInterpreter[F]] =
    Mutex[F].map(lock => FlowInterpreter(denote, bound, [A] => (fa: F[A]) => lock.lock.surround(fa), pause))
