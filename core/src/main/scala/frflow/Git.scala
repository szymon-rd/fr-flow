package frflow

import java.nio.file.Path
import java.util.concurrent.TimeUnit

/** The little FrFlow asks of git: the current commit, and a file as committed. */
object Git:
  private def run(dir: Path, args: String*): Option[String] =
    try
      val p = ProcessBuilder(("git" +: args)*).directory(dir.toFile).redirectErrorStream(false).start()
      val out = String(p.getInputStream.readAllBytes(), "UTF-8")
      if p.waitFor(20, TimeUnit.SECONDS) && p.exitValue == 0 then Some(out) else None
    catch case _: java.io.IOException => None

  /** The commit checked out in `dir`, or "" outside git. */
  def head(dir: Path): String = run(dir, "rev-parse", "HEAD").map(_.trim).getOrElse("")

  /** A file as committed at HEAD, relative to `dir`. */
  def show(dir: Path, file: String): Option[String] = run(dir, "show", s"HEAD:./$file")

  /** How files changed since a commit (working tree against it). */
  def diff(dir: Path, commit: String, files: List[String]): String =
    if commit.isEmpty then "" else run(dir, ("diff" :: commit :: "--" :: files)*).getOrElse("")
