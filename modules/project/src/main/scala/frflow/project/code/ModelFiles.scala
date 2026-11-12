package frflow.project.code

import frflow.core.name.RelPath
import scala.annotation.tailrec
import frflow.core.Theory

/** Which source files are the model's own (owner §38: in such a file only the definitions plain Scala refers to are
  * governed; every other file is governed whole), and which need no node to govern them. The model's own: each file
  * holding nodes, code given a Definition or the FrModel (`Theory.modelFiles`), and each file whose every top-level
  * definition is vocabulary (`Own.vocabulary`: Declarations, Definitions, defines, programs, models, domain types,
  * and objects holding only these). A file mixing vocabulary with plain code is governed whole, as before. A file a
  * program's body refers to (`Own.referred`) needs no node when every definition in it is vocabulary or what the
  * programs refer to (sharing's `Delivery`, the steps of `program { Delivery.run }`); it is not the model's own. A
  * helper building terms (`only`) counts as vocabulary.
  */
object ModelFiles:
  def own(t: Theory, sources: Map[RelPath, String]): Set[RelPath] =
    t.modelFiles ++ t.own.vocabulary.collect { case (f, ns) if sources.get(f).exists(only(_, ns)) => f }

  def accounted(t: Theory, sources: Map[RelPath, String]): Set[RelPath] =
    own(t, sources) ++ t.own.referred.keySet.filter(f => sources.get(f).exists(only(_,
      t.own.referred.getOrElse(f, Set.empty) ++ t.own.vocabulary.getOrElse(f, Set.empty))))

  /** Whether every top-level definition of `source` is one of `names`, a helper building terms, or an object or
    * class whose body holds only such definitions (recursively), and there is one. A helper building terms is a
    * `def` or `val` whose result type, as written, is a `Term[…]`, or a function whose final result is one
    * (`def results(u: Term[Account], q: Term[Ask]): Term[List[CrmRecord]]`): it only builds a statement's terms,
    * so what it says reaches the prover through the nodes that use it. A statement in a
    * body that is no definition (an initialiser, a call made for its effect) is plain code: the file is mixed.
    */
  def only(source: String, names: Set[String]): Boolean =
    val lines = ScalaTokens.significant(source).split("\n", -1).toVector
    val defs = definitions(lines)
    def covered(d: Def): Boolean = names(d.name) || d.buildsTerms || {
      val body = (d.line + 1 until d.end).filter(j => lines(j).trim.nonEmpty)
      val at = body.map(j => indentOf(lines(j))).minOption
      val members = defs.filter(x => x.line > d.line && x.line < d.end && at.contains(x.indent))
      val statements = body.filter(j => at.contains(indentOf(lines(j))) && !members.exists(_.line == j) &&
        !closes(lines(j)))
      members.nonEmpty && statements.isEmpty && members.forall(covered)
    }
    val top = defs.filter(_.indent == 0)
    top.nonEmpty && top.forall(covered)

  /** A line that only closes what is open (`)`, `}`, `end Mailer`): no statement of its own. */
  private def closes(l: String): Boolean = l.trim.headOption.exists(")]}".contains(_)) || l.trim.startsWith("end ")

  /** A definition: its name (`""` for an `extension` or an anonymous `given`, which no name covers), where it starts
    * and ends (the next line at its indentation or less), its indentation, and whether it is a helper building terms.
    */
  private final case class Def(name: String, line: Int, end: Int, indent: Int, buildsTerms: Boolean)

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
      val valued = m.group(2) == "def" || m.group(2) == "val"
      Def(name, i, end, indent, valued && resultType(lines.slice(i, end).mkString(" ")).exists(buildsTerms))
    }).toList

  /** A term's type, or a function's whose final result is one, as written: `Term[A]`, `A => Term[B]`; not
    * `Term[A] => IO[Unit]`. The type is read with its brackets balanced: its final result is what follows its last
    * `=>` at no depth, and it is `Term[…]` exactly, the bracket closing at its end.
    */
  def buildsTerms(t: String): Boolean =
    val last = arrows(t, 0, 0, 0, Nil).last.trim
    last.startsWith("Term[") && closing(last, "Term[".length - 1).contains(last.length - 1)

  /** The parts of a type between its `=>`s at no depth. */
  @tailrec private def arrows(t: String, k: Int, depth: Int, from: Int, done: List[String]): List[String] =
    if k >= t.length then (t.substring(from) :: done).reverse
    else t(k) match
      case '(' | '[' | '{'                                  => arrows(t, k + 1, depth + 1, from, done)
      case ')' | ']' | '}'                                  => arrows(t, k + 1, depth - 1, from, done)
      case '=' if depth == 0 && t.lift(k + 1).contains('>') =>
        arrows(t, k + 2, depth, k + 2, t.substring(from, k) :: done)
      case _                                                => arrows(t, k + 1, depth, from, done)

  /** Where the bracket opened at `at` closes, if it does. */
  private def closing(t: String, at: Int): Option[Int] =
    (at until t.length).scanLeft(0)((d, k) => d + (if "([{".contains(t(k)) then 1 else if ")]}".contains(t(k)) then -1
      else 0)).zipWithIndex.drop(1).collectFirst { case (0, j) => at + j - 1 }

  /** A definition's result type as written: what follows its last `:` at no depth before its `=` (none without one,
    * the type inferred).
    */
  def resultType(text: String): Option[String] =
    val ends = text.indices.foldLeft((0, Option.empty[Int], Option.empty[Int])) {
      case ((depth, colon, eq @ Some(_)), _) => (depth, colon, eq)
      case ((depth, colon, None), k) => text(k) match
        case '(' | '[' | '{' => (depth + 1, colon, None)
        case ')' | ']' | '}' => (depth - 1, colon, None)
        case ':' if depth == 0 => (depth, Some(k), None)
        case '=' if depth == 0 && !text.lift(k + 1).exists(c => c == '>' || c == '=') &&
            !text.lift(k - 1).exists(c => "<>!=".contains(c)) => (depth, colon, Some(k))
        case _ => (depth, colon, None)
    }
    for colon <- ends._2; eq <- ends._3 if colon < eq yield text.substring(colon + 1, eq).trim

  /** A `given` with a name of its own (`given ordering: Ordering[A] = …`), not one named only by its type. */
  private def named(l: String): Boolean = """\bgiven\s+[a-z][A-Za-z0-9_]*\s*(:|\[|\()""".r.findFirstIn(l).isDefined

  private def indentOf(l: String): Int = l.takeWhile(c => c == ' ' || c == '\t').length
