package frflow.proof.reading

/** The last line of every module FrFlow writes, which Lean prints once it has read the whole file: a file whose line
  * Lean did not print was not read to its end (Lean stopped at its error limit, crashed, ran out of memory, was
  * killed), so nothing in it is proven or shown (`Elaboration.stopped`).
  */
object Sentinel:
  private val Prefix = "frflow-end "
  private val Written = """#print\s+"(frflow-end [^"]+)"""".r

  def line(module: String): String = s"""#print "$Prefix$module""""

  /** What the file's own line makes Lean print, if it has one (FrFlow wrote it; a developer's proof file has none). */
  def of(source: String): Option[String] = Written.findFirstMatchIn(source).map(_.group(1))
