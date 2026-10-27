package frflow.testing

import cats.effect.Async
import cats.effect.std.Random
import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.name.{BoundaryName, ModelName, OpName}
import frflow.core.term.Stated
import frflow.eval.flow.{FlowInterpreter, World}
import frflow.eval.{Env, ScalaValue, Semantics}
import scala.concurrent.duration.*

/** A program with concurrent steps run on the adapters from each generated start, its branches at once and each call
  * after a random pause, `Runs` times each on adapters made afresh, for its runs to be compared with the models' (which Lean agrees with).
  * It runs the recorded `Prog`, the object Lean proves; production's interpreter (`eval.Running`) is tested
  * concurrently on its own (`RunningSuite`). Deterministic under `TestControl`.
  */
final class Interleavings[F[_]: Async: Random](semantics: Semantics, adapters: F[World[F]]):
  val Runs: Int = 8

  /** Each start's runs, each on adapters made afresh. */
  def of(steps: Prog[Stated[?]], starts: List[Env]): F[List[ScalaValue]] =
    starts.flatTraverse(start => adapters.flatMap(a => FlowInterpreter.concurrent(semantics, paused(a)))
      .flatMap(_.prog(steps, start)).replicateA(Runs))

  private def paused(adapters: World[F]): World[F] = new World[F]:
    def call(b: BoundaryName, op: OpName, args: List[ScalaValue]): F[ScalaValue] = pause *> adapters.call(b, op, args)
    def read(m: ModelName): F[ScalaValue] = adapters.read(m)
    def write(m: ModelName, s: ScalaValue): F[Unit] = adapters.write(m, s)

  private def pause: F[Unit] = Random[F].betweenLong(0, 5).flatMap(ms => Async[F].sleep(ms.millis))
