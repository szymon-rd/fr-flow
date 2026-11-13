package frflow.proof.reading

/** What `rocq compile` printed of one file, read: the error it stopped at, and what each audit printed. */
object RocqOutput:
  /** The line of the error Rocq stopped at, and what it said of it. */
  def error(output: String): Option[(Int, String)] =
    Located.findFirstMatchIn(output).map(m => m.group(1).toInt -> output.substring(m.end).trim)

  /** What Rocq said of an error, without where it is and the `Error:` it starts with. */
  def plain(output: String): String = error(output).fold(output.trim.stripPrefix("Error:").trim)(_._2)

  /** What each `Print Assumptions` printed, in order: the names of what the lemma rests on, none of one closed
    * under the global context.
    */
  def assumptions(output: String): List[List[String]] =
    output.linesIterator.foldLeft(Vector.empty[List[String]]) { (done, l) =>
      if l == Closed then done :+ Nil
      else if l == "Axioms:" then done :+ Nil
      else if Section.matches(l) then done
      else Entry.findFirstMatchIn(l).fold(done)(m =>
        if done.isEmpty then done else done.init :+ (done.last :+ m.group(1)))
    }.toList

  private val Closed = "Closed under the global context"
  private val Located = """(?m)^File "[^"]*", line (\d+), characters [-0-9]+:\s*\n?\s*Error:?""".r
  /** A heading of what an audit lists beside axioms (opaque constants, section variables). */
  private val Section = """^[A-Z][A-Za-z ]*:$""".r
  /** A name an audit lists, at the start of its line; the rest of its type is indented below. */
  private val Entry = """^([A-Za-z_][A-Za-z0-9_.']*)\s*(?::|$)""".r
