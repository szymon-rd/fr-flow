package frflow.project.port

import cats.data.NonEmptyList
import cats.effect.std.Mutex
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.project.process.{Command, Exited}
import frflow.proof.lean.ast.ModuleName
import frflow.proof.verdict.ProverRun
import java.nio.file.{Files, Path}
import scala.concurrent.duration.FiniteDuration

/** Lean's build tool in the project's Lean workspace: whether it runs, and a build of modules, with Lean's output
  * (its messages about every module built or replayed, read by `proof.reading`). Interpreters: the live one (`make`:
  * `lake build`, one build at a time, each stopped after its timeout), and a scripted one answering by module
  * (`ScriptedLake`), which tests the check's planning, caching and judges without Lean.
  */
trait Lake[F[_]]:
  def available: F[Boolean]
  def build(targets: NonEmptyList[ModuleName]): F[ProverRun]

object Lake:
  /** In `leanDir` (the project's `lean/`, made if missing): builds write the workspace's outputs, so one runs at a
    * time.
    */
  def make[F[_]: Async: Processes](leanDir: Path, lake: Command): Resource[F, Lake[F]] =
    Resource.eval(Async[F].blocking(Files.createDirectories(leanDir)) >> Mutex[F]).map(Live(leanDir, lake, _))

  /** How long `lake --version` may take. */
  val Probe: FiniteDuration = FiniteDuration(30, "seconds")

  /** `lake` in `leanDir`, its builds one at a time under `building`. */
  private final class Live[F[_]: Async: Processes](leanDir: Path, lake: Command, building: Mutex[F]) extends Lake[F]:
    def available: F[Boolean] =
      Command.run(lake.copy(timeout = Probe), List("--version"), leanDir, Map.empty)
        .map(_.ok).handleError(_ => false)

    def build(targets: NonEmptyList[ModuleName]): F[ProverRun] = building.lock.surround(
      Command.run(lake, "build" :: targets.toList.map(_.dotted), leanDir, Map.empty).map {
        case Exited.Code(0, out)  => ProverRun.Built(out)
        case Exited.Code(_, out)  => ProverRun.Failed(out)
        case Exited.TimedOut(out) => ProverRun.TimedOut(out)
      })
