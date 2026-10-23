package frflow
package check

import cats.data.NonEmptyList
import cats.effect.{IO, Ref}
import cats.effect.std.{Console, Mutex}
import cats.syntax.all.*
import fs2.io.process.ProcessBuilder
import fs2.text
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration

/** One run of a program: it finished with an exit code, or it took longer than allowed and was stopped. */
enum Run:
  case Done(exit: Int, output: String)
  case TimedOut(output: String)

  def ok: Boolean = this match
    case Done(0, _) => true
    case _ => false
  def output: String

object Run:
  /** A target an earlier batch built: nothing to run. */
  val built: Run = Done(0, "")

  /** Runs `command` in `dir`, stopped (the process killed) after `timeout` or when the fiber is cancelled. Its
    * output is stdout and stderr line by line (`merged`), or stdout alone as it came; kept when it is stopped.
    */
  def of(command: String, args: List[String], dir: Path, timeout: FiniteDuration, env: Map[String, String] = Map.empty,
      merged: Boolean = true): IO[Run] =
    Ref[IO].of(Vector.empty[String]).flatMap { out =>
      val exec = ProcessBuilder(command, args).withWorkingDirectory(fs2.io.file.Path.fromNioPath(dir)).withExtraEnv(env).spawn[IO].use { p =>
        def lines(s: fs2.Stream[IO, Byte]) = s.through(text.utf8.decode).through(text.lines)
        val read = if merged then lines(p.stdout).merge(lines(p.stderr)).evalMap(l => out.update(_ :+ l)).compile.drain
          else p.stdout.through(text.utf8.decode).evalMap(c => out.update(_ :+ c)).compile.drain &> p.stderr.compile.drain
        read *> p.exitValue
      }
      def joined(o: Vector[String]) = if merged then o.mkString("\n") else o.mkString
      exec.flatMap(code => out.get.map(o => Done(code, joined(o))))
        .timeoutTo(timeout, out.get.map(o => TimedOut(joined(o) + s"\ntimed out after ${timeout.toSeconds}s")))
    }

/** Lake in one Lean workspace, run as `cfg.lake`; each run is stopped after `cfg.timeout`. */
final class Lake private (dir: Path, cfg: Config, building: Mutex[IO]):
  /** Builds targets in one run (Lake builds them in parallel). Builds write the workspace's outputs: one at a
    * time. Elaborating and replaying only read them.
    */
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
