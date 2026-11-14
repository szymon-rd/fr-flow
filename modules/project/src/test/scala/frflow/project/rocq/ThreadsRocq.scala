package frflow.project.rocq

import java.nio.file.{Files, Path}
import scala.sys.process.{Process, ProcessLogger}

/** Rocq on generated files: the files of FrFlow's library they are over (`modules/proof/rocq/FrFlow`; those of
  * thread programs, unless others are named), then the files, each compiled after those before it.
  */
object ThreadsRocq:
  private val library = Path.of("modules/proof/rocq/FrFlow")
  private val threads = List("Threads/Prog", "Threads/Jdk", "Threads/Sem", "Threads/Lang")
  private val command: Seq[String] = sys.env.getOrElse("FRFLOW_ROCQ", "rocq compile").split(' ').toSeq

  /** `files` (each by its path, `Ox/Gen.v`, its first directory its logical root) compiled in order in a directory
    * of their own: the first that fails, with what Rocq said.
    */
  def failing(files: List[(String, String)], over: List[String] = threads): Option[(String, String)] =
    val in = Files.createTempDirectory("frflow-threads")
    val all = over.map(f => s"FrFlow/$f.v" -> Files.readString(library.resolve(s"$f.v"))) ++ files
    val roots = all.map(_._1.takeWhile(_ != '/')).distinct.flatMap(root => Seq("-Q", root, root))
    all.foldLeft(Option.empty[(String, String)]) { case (failed, (file, text)) =>
      failed.orElse {
        Files.createDirectories(in.resolve(file).getParent)
        Files.writeString(in.resolve(file), text)
        compiled(in, roots, file).map(file -> _) } }

  /** Whether Rocq finds Iris (`bin/setup-iris.sh` installs it): the logic of threads is written in it. */
  lazy val hasIris: Boolean =
    failing(List("Probe/Iris.v" -> "From iris.proofmode Require Import proofmode.\n"), Nil).isEmpty

  /** `rocq compile` on one file of `in`: what it says, if it fails. */
  private def compiled(in: Path, roots: Seq[String], file: String): Option[String] =
    val out = StringBuilder()
    def keep(line: String): Unit = { val _ = out.append(line).append('\n') }
    val code = Process(command ++ Seq("-q") ++ roots ++ Seq(file), in.toFile).!(ProcessLogger(keep, keep))
    Option.when(code != 0)(out.toString)
