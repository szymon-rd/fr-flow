package frflow
package check

import cats.data.NonEmptyList
import cats.effect.{IO, Ref, Resource}
import cats.effect.std.{Console, Mutex}
import cats.syntax.all.*
import fs2.io.process.ProcessBuilder
import fs2.text
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

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

  /** Runs `command` in `dir`, killed after `timeout` or on cancel; its output (stdout and stderr by line if `merged`) kept either way. */
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

/** The little FrFlow asks of git: the current commit, and how files changed since one. Outside git each says so. */
final class Git private (dir: Path):
  // git's output, if it ran and succeeded within 20 seconds.
  private def run(env: Map[String, String], args: String*): IO[Option[String]] =
    Run.of("git", args.toList, dir, 20.seconds, env, merged = false).map {
      case Run.Done(0, out) => Some(out)
      case _ => None
    }.handleError(_ => None)

  def head: IO[Option[String]] = run(Map.empty, "rev-parse", "HEAD").map(_.map(_.trim).filter(_.nonEmpty))

  /** The working tree against a commit, on an index of its own holding the files as they are, so a file git does not track is
    * compared as it is, not shown as deleted; the repository's index and working tree are untouched.
    */
  def diff(since: String, files: List[String]): IO[String] =
    val tempDir = Resource.make(IO.blocking(Files.createTempDirectory("frflow")))(d =>
      IO.blocking { Files.deleteIfExists(d.resolve("index")); Files.deleteIfExists(d) }.void)
    if since.isEmpty || files.isEmpty then IO.pure("")
    else tempDir.use { d =>
      val env = Map("GIT_INDEX_FILE" -> d.resolve("index").toString)
      for
        base    <- head.flatMap(h => if h.isEmpty then run(env, "read-tree", "--empty") else run(env, "read-tree", "HEAD"))
        present <- IO.blocking(files.filter(x => Files.exists(dir.resolve(x))))
        added   <- if base.isEmpty || present.isEmpty then IO.pure(base) else run(env, ("add" :: "-f" :: "--" :: present)*)
        out     <- if added.isDefined then run(env, ("diff" :: since :: "--" :: files)*) else IO.pure(None)
      yield out.getOrElse("")
    }

object Git:
  def at(dir: Path): Git = new Git(dir)
