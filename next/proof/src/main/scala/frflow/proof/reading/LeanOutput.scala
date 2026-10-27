package frflow.proof.reading

import scala.util.matching.Regex

/** Lean's output read: its messages, the axioms each audited theorem rests on, and whether a proof leans on `sorry`.
  */
object LeanOutput:
  private val LeanStyle: Regex = """^(.+?\.lean):(\d+):\d+: (error|warning|info)(?:\([^)]*\))?: ?(.*)$""".r
  private val LakeStyle: Regex = """^(error|warning|info): (.+?\.lean):(\d+):\d+: ?(.*)$""".r
  /** Lines of Lake's own: they end the message before them. */
  private val LakeLine: List[String] = List("✔", "✖", "⚠", "trace:", "Build completed", "Some required", "- ")

  /** The messages of `lean` or `lake build` output; continuation lines join the message. */
  def diagnostics(output: String): List[Diagnostic] =
    val (done, last) = output.linesIterator.foldLeft((Vector.empty[Diagnostic], Option.empty[Diagnostic])) {
      case ((done, open), line) => line match
        case LeanStyle(f, l, sev, m)                  => (done ++ open, Some(diagnostic(f, l, sev, m)))
        case LakeStyle(sev, f, l, m)                  => (done ++ open, Some(diagnostic(f, l, sev, m)))
        case _ if LakeLine.exists(line.startsWith(_)) => (done ++ open, None)
        case _                                        => (done, open.map(d => d.copy(message = s"${d.message}\n$line")))
    }
    (done ++ last).toList

  def usesSorry(output: String): Boolean =
    output.contains("declaration uses 'sorry'") || output.contains("declaration uses `sorry`")

  /** What `#print axioms` printed: each theorem's axioms (Lean wraps a long list over several lines). */
  def axioms(output: String): Map[String, List[String]] =
    val depends = """(?s)'([^'\n]+)' depends on axioms: \[(.*?)\]""".r
    val none = """'([^'\n]+)' does not depend on any axioms""".r
    // Generated files `open Classical`, so Lean prints `Classical.choice` as `choice`.
    def name(a: String) = if a == "choice" then "Classical.choice" else a
    (depends.findAllMatchIn(output).map(m =>
      m.group(1) -> m.group(2).split(",").map(_.trim).filter(_.nonEmpty).map(name).toList) ++
      none.findAllMatchIn(output).map(m => m.group(1) -> Nil)).toMap

  private def diagnostic(file: String, line: String, severity: String, message: String): Diagnostic =
    Diagnostic(file, line.toIntOption.getOrElse(0), severity == "error", message)
