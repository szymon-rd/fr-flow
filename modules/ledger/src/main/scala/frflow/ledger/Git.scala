package frflow
package ledger

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.concurrent.duration.*

/** The little FrFlow asks of git, in a working tree: the current commit, whether an object is here, the
  * code a decision saw, and how it changed since. Outside git each says so (`None`, `false`, "").
  */
trait Git:
  /** The commit checked out. */
  def head: IO[Option[String]]
  /** Whether an object (a recorded tree) is in this clone. */
  def has(obj: String): IO[Boolean]
  /** The files as they are now, written to git as a tree (HEAD's, with these files replaced), without
    * touching the index or the working tree: what a decision saw, to diff against later.
    */
  def snapshot(files: List[String]): IO[Option[String]]
  /** How files changed since a decision: the working tree against the tree (or commit) it recorded. The
    * diff runs on an index of its own holding the files as they are, so a file git does not track (a new
    * project's, before its first commit) is compared as it is, not shown as deleted.
    */
  def diff(since: String, files: List[String]): IO[String]

object Git:
  def at(dir: Path): Git = new Git:
    /** git's output, if it ran and succeeded within 20 seconds. */
    private def run(env: Map[String, String], args: String*): IO[Option[String]] =
      val start = IO.blocking {
        val pb = ProcessBuilder(("git" +: args)*).directory(dir.toFile).redirectError(ProcessBuilder.Redirect.DISCARD)
        env.foreach((k, v) => pb.environment.put(k, v))
        pb.start()
      }
      Resource.make(start)(p => IO.blocking(p.destroy())).use { p =>
        IO.interruptible(String(p.getInputStream.readAllBytes(), UTF_8)).both(IO.interruptible(p.waitFor())).map((out, code) =>
          Option.when(code == 0)(out))
      }.timeoutTo(20.seconds, IO.pure(None)).handleError(_ => None)

    def head: IO[Option[String]] = run(Map.empty, "rev-parse", "HEAD").map(_.map(_.trim).filter(_.nonEmpty))

    def has(obj: String): IO[Boolean] =
      if obj.isEmpty then IO.pure(false) else run(Map.empty, "cat-file", "-e", obj).map(_.isDefined)

    def snapshot(files: List[String]): IO[Option[String]] =
      if files.isEmpty then IO.pure(None)
      else head.flatMap(_.flatTraverse(_ => withIndex(files)(env => run(env, "write-tree"))).map(_.map(_.trim)))

    def diff(since: String, files: List[String]): IO[String] =
      if since.isEmpty || files.isEmpty then IO.pure("")
      else withIndex(files)(env => run(env, ("diff" :: since :: "--" :: files)*)).map(_.getOrElse(""))

    /** `f` run with a fresh index: HEAD's (empty before the first commit), with these files added as they
      * are now. Neither the repository's index nor the working tree is touched.
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
