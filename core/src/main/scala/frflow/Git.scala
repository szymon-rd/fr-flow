package frflow

import java.nio.file.Path
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

  /** A file as committed at HEAD, relative to `dir`. */
  def show(dir: Path, file: String): Option[String] = run(dir, "show", s"HEAD:./$file")

  /** The last `n` commits that changed a file, oldest first, with their parents in that history
    * (a merge has two) and the file as committed.
    */
  def versions(dir: Path, file: String, n: Int = 50): List[Version] =
    // Full history: a merge that kept one side's file (as `-s ours` does) is compared with each parent.
    run(dir, "log", "--full-history", "--parents", "--format=%H %P", s"-n$n", "--", file).toList
      .flatMap(_.linesIterator.map(_.trim).filter(_.nonEmpty)).reverse
      .map(_.split(" ").toList).collect { case c :: parents => Version(c, parents, run(dir, "show", s"$c:./$file")) }

  /** A commit that changed a file, its parents among such commits, and the file there (None if deleted). */
  final case class Version(commit: String, parents: List[String], text: Option[String])

  /** Whether a file is tracked by git. */
  def tracked(dir: Path, file: String): Boolean = run(dir, "ls-files", "--error-unmatch", "--", file).isDefined

  /** Whether an object (a recorded tree) is in this clone. */
  def has(dir: Path, obj: String): Boolean = obj.nonEmpty && run(dir, "cat-file", "-e", obj).isDefined

  /** The files as they are now, written to git as a tree (HEAD's, with these files replaced), without
    * touching the index or the working tree: what a decision saw, to diff against later. "" outside git.
    */
  def snapshot(dir: Path, files: List[String]): String =
    if files.isEmpty || head(dir).isEmpty then ""
    else
      val index = java.nio.file.Files.createTempDirectory("frflow").resolve("index")
      val env = Map("GIT_INDEX_FILE" -> index.toString)
      try
        val ok = runWith(dir, env, "read-tree", "HEAD").isDefined &&
          runWith(dir, env, ("add" :: "-f" :: "--" :: files.filter(f => java.nio.file.Files.exists(dir.resolve(f))))*).isDefined
        if ok then runWith(dir, env, "write-tree").map(_.trim).getOrElse("") else ""
      finally
        java.nio.file.Files.deleteIfExists(index)
        java.nio.file.Files.deleteIfExists(index.getParent)

  /** How files changed since a decision: the working tree against the tree (or commit) it recorded. */
  def diff(dir: Path, since: String, files: List[String]): String =
    if since.isEmpty then ""
    else
      // Files that are new since then (not in that tree, not yet added) are shown whole.
      val known = run(dir, ("ls-tree" :: "-r" :: "--name-only" :: "--full-name" :: since :: "--" :: files)*).toList.flatMap(_.linesIterator).toSet
      val prefix = run(dir, "rev-parse", "--show-prefix").map(_.trim).getOrElse("")
      val added = files.filterNot(f => known(prefix + f)).filter(f => java.nio.file.Files.isRegularFile(dir.resolve(f)))
        .flatMap(f => runAny(dir, "diff", "--no-index", "--", "/dev/null", f))
      run(dir, ("diff" :: since :: "--" :: files)*).getOrElse("") + added.mkString

  /** Like `run`, but also keeps the output of a command that exits 1 (`diff --no-index` with differences). */
  private def runAny(dir: Path, args: String*): Option[String] =
    try
      val p = ProcessBuilder(("git" +: args)*).directory(dir.toFile).start()
      val out = String(p.getInputStream.readAllBytes(), "UTF-8")
      if p.waitFor(20, TimeUnit.SECONDS) && p.exitValue <= 1 then Some(out) else None
    catch case _: java.io.IOException => None
