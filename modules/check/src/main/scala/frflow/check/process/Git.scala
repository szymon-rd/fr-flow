package frflow
package check
package process

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** What FrFlow asks of git: the current commit, and how files changed since one. Outside git each says so. */
final class Git private (dir: Path):
  // git's output, if it ran and succeeded within 20 seconds.
  private def run(env: Map[String, String], args: String*): IO[Option[String]] =
    Run.of("git", args.toList, dir, 20.seconds, env, merged = false).map {
      case Run.Done(0, out) => Some(out)
      case _ => None
    }.handleError(_ => None)

  def head: IO[Option[String]] = run(Map.empty, "rev-parse", "HEAD").map(_.map(_.trim).filter(_.nonEmpty))

  /** The files under `path` (relative to this directory) as committed at HEAD, with their text: None outside git, or
    * before a first commit.
    */
  def committed(path: String): IO[Option[List[(String, String)]]] =
    head.flatMap {
      case None => IO.pure(None)
      case Some(_) => run(Map.empty, "ls-tree", "-r", "--name-only", "HEAD", "--", path).flatMap {
        case None      => IO.pure(None)
        case Some(out) => out.linesIterator.map(_.trim).filter(_.nonEmpty).toList
          .traverse(f => run(Map.empty, "show", s"HEAD:./$f").map(_.map(f -> _))).map(_.sequence)
      }
    }

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
