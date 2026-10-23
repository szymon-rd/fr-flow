package frflow
package check

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** The little FrFlow asks of git, in a working tree: the current commit, and how files changed since one.
  * Outside git each says so (`None`, "").
  */
final class Git private (dir: Path):
  /** git's output, if it ran and succeeded within 20 seconds. */
  private def run(env: Map[String, String], args: String*): IO[Option[String]] =
    Run.of("git", args.toList, dir, 20.seconds, env, merged = false).map {
      case Run.Done(0, out) => Some(out)
      case _ => None
    }.handleError(_ => None)

  def head: IO[Option[String]] = run(Map.empty, "rev-parse", "HEAD").map(_.map(_.trim).filter(_.nonEmpty))

  /** How files changed since a commit: the working tree against it. The diff runs on an index of its own
    * holding the files as they are, so a file git does not track (a new project's, before its first commit)
    * is compared as it is, not shown as deleted.
    */
  def diff(since: String, files: List[String]): IO[String] =
    if since.isEmpty || files.isEmpty then IO.pure("")
    else withIndex(files)(env => run(env, ("diff" :: since :: "--" :: files)*)).map(_.getOrElse(""))

  /** `f` run with a fresh index: HEAD's (empty before the first commit), with these files added as they are
    * now. Neither the repository's index nor the working tree is touched.
    */
  private def withIndex(files: List[String])(f: Map[String, String] => IO[Option[String]]): IO[Option[String]] =
    val tempDir = Resource.make(IO.blocking(Files.createTempDirectory("frflow")))(d =>
      IO.blocking { Files.deleteIfExists(d.resolve("index")); Files.deleteIfExists(d) }.void)
    tempDir.use { d =>
      val env = Map("GIT_INDEX_FILE" -> d.resolve("index").toString)
      for
        base    <- head.flatMap(h => if h.isEmpty then run(env, "read-tree", "--empty") else run(env, "read-tree", "HEAD"))
        present <- IO.blocking(files.filter(x => Files.exists(dir.resolve(x))))
        added   <- if base.isEmpty || present.isEmpty then IO.pure(base) else run(env, ("add" :: "-f" :: "--" :: present)*)
        out     <- if added.isDefined then f(env) else IO.pure(None)
      yield out
    }

object Git:
  def at(dir: Path): Git = new Git(dir)
