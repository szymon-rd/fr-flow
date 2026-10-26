package frflow.cli
package text

import cats.effect.IO
import java.util.regex.{Matcher, Pattern}

/** Nodes as the code names them: a node's id is its val's name capitalised (`grantWhenFree`: `GrantWhenFree`), and
  * what the CLI prints says the val's name. Display only: ids, files and JSON stay as they are.
  */
object Names:
  /** The val's name of a node's id: its first letter lowered, unless the id is an acronym (`IDEA`). */
  def shown(id: String): String =
    if id.length > 1 && id(0).isUpper && id(1).isLower then s"${id(0).toLower}${id.tail}" else id

  /** `line` with each node id written as a word (not part of a path, a Lean name or a longer word) as its val's name;
    * a bold or coloured id keeps its escape codes.
    */
  def inText(ids: Iterable[String])(line: String): String =
    pattern(ids).fold(line)(p => p.matcher(line).replaceAll(m => Matcher.quoteReplacement(shown(m.group()))))

  private def pattern(ids: Iterable[String]): Option[Pattern] =
    val changed = ids.filter(id => shown(id) != id).toList.distinct.sortBy(-_.length)
    Option.when(changed.nonEmpty)(Pattern.compile(
      s"(?:(?<![A-Za-z0-9_/.])|(?<=\\u001b\\[[0-9;]{0,10}m))(?:${changed.map(Pattern.quote).mkString("|")})" +
        "(?![A-Za-z0-9_/]|\\.[A-Za-z])"))

  /** The terminal writing lines with the nodes named as the code names them; `ids`, the nodes, read once, at the
    * first line (none when they cannot be read: the lines as they are).
    */
  def terminal(t: Terminal, ids: IO[Set[String]]): Terminal = new Terminal:
    def interactive: Boolean = t.interactive
    private val read = new java.util.concurrent.atomic.AtomicReference[Option[Set[String]]](None)
    private def known: IO[Set[String]] = IO(read.get).flatMap(_.fold(
      ids.handleError(_ => Set.empty[String]).flatTap(is => IO(read.set(Some(is)))))(IO.pure))
    def out(lines: List[String]): IO[Unit] = known.flatMap(is => t.out(lines.map(inText(is))))
    def err(line: String): IO[Unit] = known.flatMap(is => t.err(inText(is)(line)))
    def read(prompt: String): IO[Option[String]] = t.read(prompt)
