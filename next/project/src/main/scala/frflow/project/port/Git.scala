package frflow.project.port

import cats.effect.{Async, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.core.name.RelPath
import frflow.project.process.{Command, Exited, Output}
import java.nio.file.{Files, Path}
import scala.concurrent.duration.FiniteDuration

/** The repository: the commit a decision is stamped with, a file as committed at it, every committed version of a
  * file (oldest first: the deciders' list's history), and the diff of governed files since a decision's commit.
  * Outside git, or before a first commit, each says there is none. Interpreters: the `git` command (`make`), and
  * commits in memory (`MemoryGit`) for the decision tests. Laws: `committed(p)` is the last of `versions(p)`; both are
  * empty when `head` is.
  */
trait Git[F[_]]:
  def head: F[Option[String]]
  def committed(p: RelPath): F[Option[String]]
  def versions(p: RelPath): F[List[String]]
  def diff(since: String, files: List[RelPath]): F[String]

object Git:
  def make[F[_]: Async: Processes](dir: Path): Git[F] = Live(dir)

  /** The `git` command in `dir`, each run stopped after 20 seconds; a run that fails says there is none. */
  private final class Live[F[_]: Async: Processes](dir: Path) extends Git[F]:
    private val git = Command("git", FiniteDuration(20, "seconds"), Output.Standard)

    /** Git's output, when it ran and succeeded. */
    private def run(env: Map[String, String], args: String*): F[Option[String]] =
      Command.run(git, args.toList, dir, env).map {
        case Exited.Code(0, out) => Some(out)
        case _                   => None
      }.handleError(_ => None)

    def head: F[Option[String]] = run(Map.empty, "rev-parse", "--verify", "-q", "HEAD")
      .map(_.map(_.trim).filter(_.nonEmpty))

    def committed(p: RelPath): F[Option[String]] =
      head.flatMap(_.flatTraverse(_ => run(Map.empty, "show", s"HEAD:./${p.value}")))

    def versions(p: RelPath): F[List[String]] =
      run(Map.empty, "log", "--format=%H", "--reverse", "--", p.value).flatMap(_.toList
        .flatMap(_.linesIterator.map(_.trim).filter(_.nonEmpty))
        .traverseFilter(c => run(Map.empty, "show", s"$c:./${p.value}")))

    /** The working tree against a commit, on an index of its own holding the files as they are, so a file git does
      * not track is compared as it is; the repository's index and working tree are untouched.
      */
    def diff(since: String, files: List[RelPath]): F[String] =
      val scratch = Resource.make(Async[F].blocking(Files.createTempDirectory("frflow")))(d =>
        Async[F].blocking(List(d.resolve("index"), d).foreach(f => Files.deleteIfExists(f): Unit)))
      if since.isEmpty || files.isEmpty then "".pure[F]
      else scratch.use { d =>
        val env = Map("GIT_INDEX_FILE" -> d.resolve("index").toString)
        val names = files.map(_.value)
        for
          base    <- head.flatMap(h => run(env, "read-tree", h.fold("--empty")(_ => "HEAD")))
          present <- Async[F].blocking(names.filter(x => Files.exists(dir.resolve(x))))
          added   <- if base.isEmpty || present.isEmpty then base.pure[F]
                     else run(env, ("add" :: "-f" :: "--" :: present)*)
          out     <- added.flatTraverse(_ => run(env, ("diff" :: since :: "--" :: names)*))
        yield out.getOrElse("")
      }
