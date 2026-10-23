package frflow
package check

import cats.data.NonEmptyList
import cats.effect.{IO, Ref}
import cats.effect.std.{Console, Mutex}
import cats.syntax.all.*
import fs2.io.process.ProcessBuilder
import fs2.text
import java.nio.file.Path

/** One run of Lean: it finished with an exit code, or it took longer than allowed and was stopped. */
enum Run:
  case Done(exit: Int, output: String)
  case TimedOut(output: String)

  def ok: Boolean = this match
    case Done(0, _) => true
    case _ => false
  /** What Lean printed, stdout and stderr each line by line. */
  def output: String

object Run:
  /** A target an earlier batch built: nothing to run. */
  val built: Run = Done(0, "")

/** Lake in one Lean workspace. */
trait Lake:
  /** Builds targets in one run (Lake builds them in parallel). Builds write the workspace's outputs: one
    * at a time. Elaborating and replaying only read them.
    */
  def build(targets: NonEmptyList[String]): IO[Run]
  def build(target: String): IO[Run] = build(NonEmptyList.one(target))
  /** Elaborates one file (a path relative to the workspace, or absolute). */
  def elaborate(file: String): IO[Run]
  /** Whether Lake runs at all. */
  def available: IO[Boolean]

object Lake:
  /** Lake in `dir`, run as `cfg.lake`; each run is stopped (the process killed) after `cfg.timeout`, or
    * when the fiber running it is cancelled.
    */
  def apply(dir: Path, cfg: Config): IO[Lake] = Mutex[IO].map { building =>
    new Lake:
      def build(targets: NonEmptyList[String]): IO[Run] = building.lock.surround(run("build" :: targets.toList))
      def elaborate(file: String): IO[Run] = run(List("env", "lean", file))
      def available: IO[Boolean] = spawn(List("--version")).map(_.ok).handleError(_ => false)

      private def run(args: List[String]): IO[Run] =
        if !cfg.timing then spawn(args)
        else spawn(args).timed.flatTap((t, _) =>
          Console[IO].errorln(f"[lean ${t.toMillis / 1e3}%.1fs] ${args.mkString(" ").take(140)}")).map(_._2)

      // The output as it came, stdout and stderr each line by line; kept when the run is stopped.
      private def spawn(args: List[String]): IO[Run] = Ref[IO].of(Vector.empty[String]).flatMap { out =>
        val exec = ProcessBuilder(cfg.lake, args).withWorkingDirectory(fs2.io.file.Path.fromNioPath(dir)).spawn[IO].use { p =>
          def lines(s: fs2.Stream[IO, Byte]) = s.through(text.utf8.decode).through(text.lines)
          lines(p.stdout).merge(lines(p.stderr)).evalMap(l => out.update(_ :+ l)).compile.drain *> p.exitValue
        }
        def joined(o: Vector[String]) = o.mkString("\n")
        exec.flatMap(code => out.get.map(o => Run.Done(code, joined(o))))
          .timeoutTo(cfg.timeout, out.get.map(o => Run.TimedOut(joined(o) + s"\ntimed out after ${cfg.timeout.toSeconds}s")))
      }
  }
