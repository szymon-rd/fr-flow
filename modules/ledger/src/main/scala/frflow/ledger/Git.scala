package frflow
package ledger

import java.nio.file.{Files, Path}
import java.util.concurrent.TimeUnit

/** The little FrFlow asks of git: the current commit, a file as committed, and the code a decision saw. */
object Git:
  private def run(dir: Path, args: String*): Option[String] = runWith(dir, Map.empty, args*)

  private def runWith(dir: Path, env: Map[String, String], args: String*): Option[String] =
    try
      val pb = ProcessBuilder(("git" +: args)*).directory(dir.toFile).redirectErrorStream(false)
      env.foreach((k, v) => pb.environment.put(k, v))
      val p = pb.start()
      val out = String(p.getInputStream.readAllBytes(), "UTF-8")
      if p.waitFor(20, TimeUnit.SECONDS) && p.exitValue == 0 then Some(out) else None
    catch case _: java.io.IOException => None

  /** The commit checked out in `dir`, or "" outside git. */
  def head(dir: Path): String = run(dir, "rev-parse", "HEAD").map(_.trim).getOrElse("")

  /** Whether an object (a recorded tree) is in this clone. */
  def has(dir: Path, obj: String): Boolean = obj.nonEmpty && run(dir, "cat-file", "-e", obj).isDefined

  /** The files as they are now, written to git as a tree (HEAD's, with these files replaced), without
    * touching the index or the working tree: what a decision saw, to diff against later. "" outside git.
    */
  def snapshot(dir: Path, files: List[String]): String =
    if files.isEmpty || head(dir).isEmpty then ""
    else withIndex(dir, files)(env => runWith(dir, env, "write-tree").map(_.trim)).getOrElse("")

  /** How files changed since a decision: the working tree against the tree (or commit) it recorded.
    * The diff runs on an index of its own holding the files as they are, so a file git does not track
    * (a new project's, before its first commit) is compared as it is, not shown as deleted.
    */
  def diff(dir: Path, since: String, files: List[String]): String =
    if since.isEmpty || files.isEmpty then ""
    else withIndex(dir, files)(env => runWith(dir, env, ("diff" :: since :: "--" :: files)*)).getOrElse("")

  /** `f` run with a fresh index: HEAD's (empty before the first commit), with these files added as
    * they are now. Neither the repository's index nor the working tree is touched.
    */
  private def withIndex[A](dir: Path, files: List[String])(f: Map[String, String] => Option[A]): Option[A] =
    val index = Files.createTempDirectory("frflow").resolve("index")
    val env = Map("GIT_INDEX_FILE" -> index.toString)
    try
      val base = if head(dir).isEmpty then runWith(dir, env, "read-tree", "--empty") else runWith(dir, env, "read-tree", "HEAD")
      val present = files.filter(x => Files.exists(dir.resolve(x)))
      if base.isDefined && (present.isEmpty || runWith(dir, env, ("add" :: "-f" :: "--" :: present)*).isDefined) then f(env) else None
    finally
      Files.deleteIfExists(index)
      Files.deleteIfExists(index.getParent)
