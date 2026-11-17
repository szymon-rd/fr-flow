package frflow.project.rocq

import java.nio.file.{Files, Path}
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration
import scala.sys.process.{Process, ProcessLogger}

/** Rocq on generated files: the files of FrFlow's library they are over (`modules/proof/rocq/FrFlow`), then the
  * files, each compiled after those before it.
  */
object ThreadsRocq:
  private val library = Path.of("modules/proof/rocq/FrFlow")
  private val command: Seq[String] = sys.env.getOrElse("FRFLOW_ROCQ", "rocq compile").split(' ').toSeq

  /** The files of the library named in `over`, then `files` (each by its path, `Ox/Tree/All.v`, its first directory
    * its logical root), compiled in order in a directory of their own: the first that fails, with what Rocq said.
    */
  def failing(files: List[(String, String)], over: List[String]): Option[(String, String)] =
    failingTogether(files, over, Nil)

  /** As `failing`; then the files of `together`, each over all of those and none over another, compiled at once:
    * the first that fails.
    */
  def failingTogether(files: List[(String, String)], over: List[String], together: List[(String, String)])
      : Option[(String, String)] =
    val in = Files.createTempDirectory("frflow-threads")
    val all = over.map(f => s"FrFlow/$f.v" -> Files.readString(library.resolve(s"$f.v"))) ++ files
    val roots = all.map(_._1.takeWhile(_ != '/')).distinct.flatMap(root => Seq("-Q", root, root))
    def one(file: String, text: String): Option[(String, String)] =
      Files.createDirectories(in.resolve(file).getParent)
      Files.writeString(in.resolve(file), text)
      compiled(in, roots, file).map(file -> _)
    all.foldLeft(Option.empty[(String, String)]) { case (failed, (file, text)) => failed.orElse(one(file, text)) }
      .orElse {
        given ExecutionContext = ExecutionContext.global
        val running = together.map((file, text) => Future(one(file, text)))
        running.map(Await.result(_, Duration.Inf)).collectFirst { case Some(failed) => failed } }

  /** `rocq compile` on one file of `in`: what it says, if it fails. */
  private def compiled(in: Path, roots: Seq[String], file: String): Option[String] =
    val out = StringBuilder()
    def keep(line: String): Unit = { val _ = out.append(line).append('\n') }
    val code = Process(command ++ Seq("-q") ++ roots ++ Seq(file), in.toFile).!(ProcessLogger(keep, keep))
    Option.when(code != 0)(out.toString)
