package frflow.check

import java.nio.file.Path
import java.util.concurrent.TimeUnit
import scala.util.matching.Regex

final case class ProcessResult(exitCode: Int, output: String):
  def ok: Boolean = exitCode == 0

/** A diagnostic reported by Lean, with its position in `file` (as Lean printed it). */
final case class Diagnostic(file: String, line: Int, col: Int, severity: String, message: String):
  def isError: Boolean = severity == "error"
  def isSorry: Boolean = severity == "warning" && message.contains("declaration uses `sorry`") ||
    severity == "warning" && message.contains("declaration uses 'sorry'")

/** Thin wrapper around `lake`. The executable is taken from `FRFLOW_LAKE`, or `lake` on the PATH. */
final class LeanRunner(leanDir: Path, timeoutSeconds: Long = 900):
  private val lake: String = sys.env.getOrElse("FRFLOW_LAKE", "lake")

  def build(targets: String*): ProcessResult = run(Seq(lake, "build") ++ targets)

  /** Elaborates a single file in the workspace environment. */
  def elaborate(relFile: String): ProcessResult = run(Seq(lake, "env", "lean", relFile))

  def available: Boolean =
    try run(Seq(lake, "--version")).ok
    catch case _: java.io.IOException => false

  private def run(cmd: Seq[String]): ProcessResult =
    val pb = new ProcessBuilder(cmd*).directory(leanDir.toFile).redirectErrorStream(true)
    val proc = pb.start()
    val out = new java.io.ByteArrayOutputStream()
    val pump = new Thread(() => { proc.getInputStream.transferTo(out); () })
    pump.start()
    if !proc.waitFor(timeoutSeconds, TimeUnit.SECONDS) then
      proc.destroyForcibly()
      pump.join(1000)
      ProcessResult(124, out.toString("UTF-8") + s"\n[frflow] timed out after ${timeoutSeconds}s: ${cmd.mkString(" ")}")
    else
      pump.join()
      ProcessResult(proc.exitValue(), out.toString("UTF-8"))

object Diagnostics:
  // `lean` prints   path:line:col: error: message
  // `lake build` prints   error: path:line:col: message
  private val LeanStyle: Regex = """^(.+?\.lean):(\d+):(\d+): (error|warning|info): ?(.*)$""".r
  private val LakeStyle: Regex = """^(error|warning|info): (.+?\.lean):(\d+):(\d+): ?(.*)$""".r

  /** Parses diagnostics; continuation lines are appended to the preceding message. */
  def parse(output: String): Seq[Diagnostic] =
    val out = Seq.newBuilder[Diagnostic]
    var current: Option[Diagnostic] = None
    def flush(): Unit = current.foreach(d => out += d.copy(message = d.message.trim))
    output.linesIterator.foreach {
      case LeanStyle(f, l, c, sev, msg) =>
        flush(); current = Some(Diagnostic(f, l.toInt, c.toInt, sev, msg))
      case LakeStyle(sev, f, l, c, msg) =>
        flush(); current = Some(Diagnostic(f, l.toInt, c.toInt, sev, msg))
      case line if line.startsWith("✔") || line.startsWith("✖") || line.startsWith("⚠") ||
          line.startsWith("trace:") || line.startsWith("Some required targets") ||
          line.startsWith("Build completed") || line.startsWith("- ") =>
        flush(); current = None
      case line =>
        current = current.map(d => d.copy(message = d.message + "\n" + line))
    }
    flush()
    out.result()

  /** Parses `#print axioms` output into theorem -> axioms. */
  def parseAxioms(output: String): Map[String, Set[String]] =
    val Depends = """^'(.+?)' depends on axioms: \[(.*)\]\s*$""".r
    val NoAxioms = """^'(.+?)' does not depend on any axioms\s*$""".r
    output.linesIterator.collect {
      case Depends(thm, axs) => thm -> axs.split(",").map(_.trim).filter(_.nonEmpty).toSet
      case NoAxioms(thm)     => thm -> Set.empty[String]
    }.toMap
