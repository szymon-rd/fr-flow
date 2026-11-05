package frflow.project.code

import frflow.core.name.RelPath
import frflow.core.Theory

/** Which source files are the model's own (owner §38: in such a file only the definitions plain Scala refers to are
  * governed; every other file is governed whole), and which need no node to govern them. The model's own: each file
  * holding nodes, code given a Definition or the FrModel (`Theory.modelFiles`), and each file whose every top-level
  * definition is vocabulary (`Own.vocabulary`: Declarations, Definitions, defines, programs, models, domain types,
  * and objects holding only these). A file mixing vocabulary with plain code is governed whole, as before. A file a
  * program's body refers to (`Own.referred`) needs no node when every definition in it is vocabulary or what the
  * programs refer to (sharing's `Delivery`, the steps of `program { Delivery.run }`); it is not the model's own.
  */
object ModelFiles:
  def own(t: Theory, sources: Map[RelPath, String]): Set[RelPath] =
    t.modelFiles ++ t.own.vocabulary.collect { case (f, ns) if sources.get(f).exists(only(_, ns)) => f }

  def accounted(t: Theory, sources: Map[RelPath, String]): Set[RelPath] =
    own(t, sources) ++ t.own.referred.keySet.filter(f => sources.get(f).exists(only(_,
      t.own.referred.getOrElse(f, Set.empty) ++ t.own.vocabulary.getOrElse(f, Set.empty))))

  /** Whether every top-level definition of `source` is one of `names`, or an object or class all of whose members
    * are (recursively), and there is one.
    */
  def only(source: String, names: Set[String]): Boolean =
    val defs = definitions(ScalaTokens.significant(source).split("\n", -1).toVector)
    def covered(d: Def): Boolean = names(d.name) || {
      val inside = defs.filter(x => x.line > d.line && x.line < d.end && x.indent > d.indent)
      val members = inside.filter(_.indent == inside.map(_.indent).minOption.getOrElse(0))
      members.nonEmpty && members.forall(covered)
    }
    val top = defs.filter(_.indent == 0)
    top.nonEmpty && top.forall(covered)

  /** A definition: its name (`""` for an `extension` or an anonymous `given`, which no name covers), where it starts
    * and ends (the next line at its indentation or less), and its indentation.
    */
  private final case class Def(name: String, line: Int, end: Int, indent: Int)

  private val Starts = ("""^(\s*)(?:@\w+\s+)*(?:(?:private|protected|final|sealed|abstract|override|implicit|lazy|""" +
    """inline|transparent|case|open|opaque)\s+|private\[\w+\]\s+)*(def|val|var|object|class|trait|enum|type|""" +
    """given|extension)\b\s*([A-Za-z_][A-Za-z0-9_]*)?""").r

  private def definitions(lines: Vector[String]): List[Def] =
    lines.zipWithIndex.flatMap((l, i) => Starts.findFirstMatchIn(l).map { m =>
      val indent = m.group(1).length
      val end = lines.indices.find(j => j > i && indentOf(lines(j)) <= indent && !lines(j).trim.startsWith(")"))
        .getOrElse(lines.size)
      val name = if m.group(2) == "extension" || (m.group(2) == "given" && !named(l)) then "" else
        Option(m.group(3)).getOrElse("")
      Def(name, i, end, indent)
    }).toList

  /** A `given` with a name of its own (`given ordering: Ordering[A] = …`), not one named only by its type. */
  private def named(l: String): Boolean = """\bgiven\s+[a-z][A-Za-z0-9_]*\s*(:|\[|\()""".r.findFirstIn(l).isDefined

  private def indentOf(l: String): Int = l.takeWhile(c => c == ' ' || c == '\t').length
