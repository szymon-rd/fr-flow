package frflow.api.derive

import frflow.core.name.RelPath

/** What a word means, as its Scaladoc says: the `/** … */` right above `val name =` in the file it is written in,
  * read from the sources the analysis read, as one line of text. A `define` has no sentence of its own beside its
  * body; its comment is that sentence.
  */
private[api] object DocComments:
  /** The comment above `val name` in the first of `files` (as the model records them) that has one. */
  def of(name: String, files: List[RelPath], sources: Map[RelPath, String]): Option[String] =
    files.iterator.flatMap(f => text(f, sources)).flatMap(above(name, _)).nextOption()

  /** The source of `f`, by its path or, as the model may record it from the build's directory, by its ending. */
  private def text(f: RelPath, sources: Map[RelPath, String]): Option[String] =
    sources.get(f).orElse(sources.collectFirst { case (p, t) if f.value.endsWith("/" + p.value) ||
      p.value.endsWith("/" + f.value) => t })

  /** The last Scaladoc directly above a `val name =` of `text` (modifiers between allowed), tidied to one line. */
  def above(name: String, text: String): Option[String] =
    val decl = (raw"(?s)/\*\*((?:(?!\*/).)*)\*/\s*(?:(?:private|protected|override|lazy|final)\s+)*val\s+" +
      java.util.regex.Pattern.quote(name) + raw"\b").r
    decl.findAllMatchIn(text).toList.lastOption.map(m => tidy(m.group(1))).filter(_.nonEmpty)

  /** A comment's text: each line without its leading `*`, joined by spaces. */
  private def tidy(body: String): String =
    body.linesIterator.map(_.trim.stripPrefix("*").trim).filter(_.nonEmpty).mkString(" ")
