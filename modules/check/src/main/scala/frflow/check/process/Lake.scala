package frflow
package check
package process

import cats.data.NonEmptyList
import cats.effect.IO
import cats.effect.std.{Console, Mutex}
import java.nio.file.Path

/** Lake in one Lean workspace, run as `cfg.lake`; each run is stopped after `cfg.timeout`. */
final class Lake private (dir: Path, cfg: Config, building: Mutex[IO]):
  /** One run builds them all, in parallel; builds write the workspace's outputs, so one at a time (elaborating only reads them). */
  def build(targets: NonEmptyList[String]): IO[Run] = building.lock.surround(run("build" :: targets.toList))
  def build(target: String): IO[Run] = build(NonEmptyList.one(target))
  /** Elaborates one file (a path relative to the workspace, or absolute). */
  def elaborate(file: String): IO[Run] = run(List("env", "lean", file))
  def available: IO[Boolean] = spawn(List("--version")).map(_.ok).handleError(_ => false)

  private def spawn(args: List[String]) = Run.of(cfg.lake, args, dir, cfg.timeout)

  private def run(args: List[String]): IO[Run] =
    if !cfg.timing then spawn(args)
    else spawn(args).timed.flatTap((t, _) =>
      Console[IO].errorln(f"[lean ${t.toMillis / 1e3}%.1fs] ${args.mkString(" ").take(140)}")).map(_._2)

object Lake:
  def apply(dir: Path, cfg: Config): IO[Lake] = Mutex[IO].map(new Lake(dir, cfg, _))
