package frflow
package ledger

/** IDEA.md as the decisions read it: what a root is decided against, by section, and what is not
  * modelled.
  */
object Idea:

  /** The `## ` sections of the idea (without Not modelled), by heading, after the text before the
    * first one (which every section-root is also decided against).
    */
  def sections(decided: String): (String, List[(String, String)]) =
    val (intro, rest) = decided.linesIterator.toList.span(l => !l.startsWith("## "))
    def go(ls: List[String]): List[(String, String)] = ls match
      case h :: tail =>
        val (body, more) = tail.span(l => !l.startsWith("## "))
        (h.stripPrefix("## ").trim -> (h :: body).mkString("\n").trim) :: go(more)
      case Nil => Nil
    (intro.mkString("\n").trim, go(rest))

  /** IDEA.md split into the idea a root is decided against, and its `## Not modelled` section. */
  def split(idea: String): (String, String) =
    val lines = idea.linesIterator.toList
    lines.indexWhere(_.trim.toLowerCase.startsWith("## not modelled")) match
      case -1 => (idea.trim, "")
      case i =>
        val (section, rest) = lines.drop(i + 1).span(l => !(l.startsWith("# ") || l.startsWith("## ")))
        ((lines.take(i) ++ rest).mkString("\n").trim, section.mkString("\n").trim)
