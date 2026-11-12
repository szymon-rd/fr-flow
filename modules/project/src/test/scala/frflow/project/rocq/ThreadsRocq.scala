package frflow.project.rocq

import java.nio.file.{Files, Path}
import scala.sys.process.{Process, ProcessLogger}

/** Rocq on files of thread programs: the library they are over (`modules/proof/rocq/FrFlow/Threads`), then the
  * files, each compiled after those before it.
  */
object ThreadsRocq:
  private val library = Path.of("modules/proof/rocq/FrFlow/Threads")
  private val command: Seq[String] = sys.env.getOrElse("FRFLOW_ROCQ", "rocq compile").split(' ').toSeq

  /** `files` (each by its path, `Ox/Gen.v`, its first directory its logical root) compiled in order in a directory
    * of their own: the first that fails, with what Rocq said.
    */
  def failing(files: List[(String, String)]): Option[(String, String)] =
    val in = Files.createTempDirectory("frflow-threads")
    val all = List("Prog", "Jdk", "Sem", "Lang").map(f => s"FrFlow/Threads/$f.v" ->
      Files.readString(library.resolve(s"$f.v"))) ++ files
    val roots = all.map(_._1.takeWhile(_ != '/')).distinct.flatMap(root => Seq("-Q", root, root))
    all.foldLeft(Option.empty[(String, String)]) { case (failed, (file, text)) =>
      failed.orElse {
        Files.createDirectories(in.resolve(file).getParent)
        Files.writeString(in.resolve(file), text)
        compiled(in, roots, file).map(file -> _) } }

  /** `rocq compile` on one file of `in`: what it says, if it fails. */
  private def compiled(in: Path, roots: Seq[String], file: String): Option[String] =
    val out = StringBuilder()
    def keep(line: String): Unit = { val _ = out.append(line).append('\n') }
    val code = Process(command ++ Seq("-q") ++ roots ++ Seq(file), in.toFile).!(ProcessLogger(keep, keep))
    Option.when(code != 0)(out.toString)
