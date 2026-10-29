package frflow.project.code

import scala.annotation.tailrec

/** The definitions of a source named, as a fingerprint reads them (owner §38): each from its line to the next line at
  * its indentation or less, with the same source's definitions those name, in the order they are written. The source
  * is as the simple lexer leaves it (`ScalaTokens.significant`): comments blanked, blank lines dropped, indentation
  * kept.
  */
object Definitions:
  private val Starts = ("""^(\s*)(?:(?:private|protected|final|sealed|abstract|override|implicit|lazy|inline|""" +
    """transparent|case|open|opaque)\s+|private\[\w+\]\s+)*(?:def|val|var|object|class|trait|enum|type|given)\s+""" +
    """([A-Za-z_][A-Za-z0-9_]*)""").r
  private val Word = """[A-Za-z_][A-Za-z0-9_]*""".r

  def of(source: String, names: List[String]): String =
    val lines = source.split("\n", -1).toVector
    val spans = starts(lines)
    val kept = closure(lines, spans, names.toSet.intersect(spans.keySet), Set.empty)
    spans.toList.filter((n, _) => kept(n)).flatMap(_._2).flatMap((from, to) => from until to).distinct.sorted
      .map(lines).mkString("\n")

  /** Each definition's spans, by name: from its line to the next at its indentation or less. */
  private def starts(lines: Vector[String]): Map[String, List[(Int, Int)]] =
    lines.zipWithIndex.flatMap((l, i) => Starts.findFirstMatchIn(l).map { m =>
      val indent = m.group(1).length
      val end = lines.indices.find(j => j > i && indentOf(lines(j)) <= indent).getOrElse(lines.size)
      m.group(2) -> (i, end)
    }).toList.groupMap(_._1)(_._2)

  private def indentOf(l: String): Int = l.takeWhile(c => c == ' ' || c == '\t').length

  /** The names reached from `todo` through the words their spans hold. */
  @tailrec private def closure(lines: Vector[String], spans: Map[String, List[(Int, Int)]], todo: Set[String],
      done: Set[String]): Set[String] =
    if todo.isEmpty then done
    else
      val all = done ++ todo
      val named = todo.flatMap(spans.getOrElse(_, Nil)).flatMap((from, to) => lines.slice(from, to))
        .flatMap(Word.findAllIn).filter(spans.contains)
      closure(lines, spans, named -- all, all)
