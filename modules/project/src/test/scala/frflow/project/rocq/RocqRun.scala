package frflow.project.rocq

import frflow.proof.rocq.RocqProject
import java.nio.file.{Files, Path}
import scala.sys.process.{Process, ProcessLogger}

/** A generated project's Rocq, checked by `coqc`: each file compiled after those it imports. `coqc` stops at a
  * file's first error, so a lemma whose proof fails is admitted and the file compiled again: the lemmas not
  * proven are those admitted (`open`); a file with any other error is `broken`, and so is one that imports it.
  */
object RocqRun:
  final case class Checked(compiled: List[String], open: Map[String, List[String]], broken: Map[String, String],
      stated: Map[String, List[String]] = Map.empty):
    def proven(file: String, lemma: String): Boolean =
      compiled.contains(file) && !open.get(file).exists(_.contains(lemma))

  /** The lemmas a file checked states, in order. */
  def lemmas(checked: Checked, file: String): List[String] = checked.stated.getOrElse(file, Nil)

  /** Rocq's compiler: `rocq compile`, or what `FRFLOW_ROCQ` names (`coqc` of a Rocq before 9). */
  private val command: Seq[String] = sys.env.getOrElse("FRFLOW_ROCQ", "rocq compile").split(' ').toSeq

  private val library: Path = Path.of("modules/proof/rocq/FrFlow/Base.v").toAbsolutePath

  def check(project: RocqProject, in: Path): Checked =
    Files.createDirectories(in.resolve("FrFlow"))
    Files.writeString(in.resolve("FrFlow/Base.v"), Files.readString(library))
    compile(in, "FrFlow/Base.v").foreach(e => throw AssertionError(s"FrFlow's Rocq library does not compile: $e"))
    project.files.foldLeft(Checked(Nil, Map.empty, Map.empty)) { case (done, (file, text)) =>
      Files.createDirectories(in.resolve(file).getParent)
      Files.writeString(in.resolve(file), text)
      admitting(in, file, Nil) match
        case Right(open)  => done.copy(compiled = done.compiled :+ file, open = done.open + (file -> open),
          stated = done.stated + (file -> named(text)))
        case Left(error)  => done.copy(broken = done.broken + (file -> error))
    }

  /** The file compiled, each lemma whose proof fails admitted in turn: those admitted, or another error. */
  private def admitting(in: Path, file: String, open: List[String]): Either[String, List[String]] =
    compile(in, file) match
      case None        => Right(open)
      case Some(error) =>
        val lines = Files.readString(in.resolve(file)).split("\n", -1).toVector
        val at = "line (\\d+), characters [-0-9]+:\\s+Error".r.findFirstMatchIn(error).map(_.group(1).toInt - 1)
        at.filter(i => i >= 1 && lines(i).startsWith("Proof.") && !lines(i).endsWith("Admitted.") &&
          lines(i - 1).startsWith("Lemma ")) match
          case Some(i) =>
            Files.writeString(in.resolve(file), lines.updated(i, "Proof. Admitted.").mkString("\n"))
            admitting(in, file, open :+ lemma(lines(i - 1)))
          case None    => Left(error.linesIterator.take(6).mkString(" | "))

  private def named(text: String): List[String] =
    text.linesIterator.filter(_.startsWith("Lemma ")).map(lemma).toList
  private def lemma(line: String): String = line.stripPrefix("Lemma ").takeWhile(c => c != ' ' && c != ':')

  /** `coqc` on one file: its error, if it has one. */
  private def compile(in: Path, file: String): Option[String] =
    val out = StringBuilder()
    def keep(line: String): Unit = { val _ = out.append(line).append('\n') }
    val log = ProcessLogger(keep, keep)
    val code = Process(command ++ Seq("-q", "-Q", "FrFlow", "FrFlow", "-Q", "FrFlowGen", "FrFlowGen", file),
      in.toFile).!(log)
    Option.when(code != 0)(out.toString)
