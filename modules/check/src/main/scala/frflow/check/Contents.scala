package frflow
package check

import frflow.ledger.Idea
import frflow.protocol.Content
import io.circe.Json

/** A node as the developer sees it and decides it. A decision is bound to its hash. A statement's parts
  * are part of it (docs/DAG.md §5): a part added or removed reviews it, with the cause `parts`.
  */
object Contents:
  private def str(s: String): Json = Json.fromString(s)
  private def strs(xs: Seq[String]): Json = Json.fromValues(xs.map(Json.fromString))

  def of(a: Analysis, n: Node[?]): Content =
    val kb = a.kb
    Content((Seq(
      "kind" -> str(n.kind.toString),
      "parents" -> strs(n.parents.map(_.id))) ++
      Option.when(kb.isStatement(n))("parts" -> strs(kb.parts(n).map(_.id))) ++ Seq(
      "statement" -> str(n.statement),
      "why" -> str(n.why),
      "sources" -> Json.obj(Seq("formula" -> n.formula, "post" -> n.post, "rule" -> n.rule, "check" -> n.local).collect { case (k, Some(l)) => k -> str(l.source) }*),
      "substitutions" -> strs(n.substs.map(s => s"${s.name} := ${s.term.fold(s.lean)(_.source)}")),
      "examples" -> strs(n.cases.map(_.describe)),
      "vocabulary" -> strs(vocabulary(kb, n)),
      "uses" -> strs(a.generate.sourcesUsedBy(n)),
      "governs" -> strs(n.governs),
      "definition" -> str(a.definition(n))
    ) ++ n.op.map(o => "op" -> str(o.name)) ++ n.replaced.map(r => "replaces" -> str(r.id)) ++
      (if n.kept.isEmpty then Nil else List("keeps" -> strs(n.kept.map(_.describe)))) ++
      (if n.expected.isEmpty then Nil else List("expects" -> strs(n.expected.map((st, l) => s"$st: ${l.source}")))) ++
      implementation(kb, n).map("implementation" -> str(_)) ++
      idea(a, n))*)

  /** How a contract is implemented: the proven define and what it is made of, and the running code. */
  private def implementation(kb: KnowledgeBase, n: Node[?]): Option[String] =
    kb.implementation(n).flatMap { i =>
      val proven = i.proven.toList.flatMap(d => s"proven: ${d.name}" +: Def.closure(List(d)).map(x => s"${x.name} = ${x.lifted.source}"))
      val runs = Option.when(i.wiring.nonEmpty)(if i.proven.isDefined then s"runs: ${i.wiring}" else i.wiring).toList
      Option.when((proven ++ runs).nonEmpty)((proven ++ runs).mkString("\n"))
    }

  /** The root is decided against the idea's title and lead; a node naming a section, against that section. */
  private def idea(a: Analysis, n: Node[?]): Seq[(String, Json)] =
    if n.ideaSection.nonEmpty then Seq("idea" -> str(a.ideaOf(n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(a.notModelled))
    else if a.kb.isRoot(n) then Seq("idea" -> str(Idea.sections(a.ideaDecided)._1), "notModelled" -> str(a.notModelled))
    else Nil

  /** The terms a node mentions, with what they mean in the world. */
  def vocabulary(kb: KnowledgeBase, n: Node[?]): List[String] =
    val terms = kb.termsOf(n).toSet ++ n.defines
    (kb.opaques.filter(o => terms(o.name)).map(o => s"${o.name}: ${o.means}") ++
      kb.params.filter(p => terms(p.name)).map(p => s"${p.name}: ${p.means}")).sorted

  private val Statement = """^\s*(?:(?:private|protected|final|lazy|override|inline)\s+)*(?:val|def|given|var)\b.*""".r

  /** The source of the top-level definition at offset `at` of a file's text (the `val` with every call
    * chained on it, its arguments, its examples): what the developer decides is what is written, so nothing
    * hidden in an argument (a block that runs code before giving a `why`) escapes review.
    */
  def definition(text: String, at: Int): String =
    val lines = text.split("\n", -1).toList
    val starts = lines.scanLeft(0)(_ + _.length + 1)
    val k = starts.lastIndexWhere(_ <= at).min(lines.size - 1).max(0)
    def indent(l: String) = l.takeWhile(_ == ' ').length
    def comment(t: String) = Seq("//", "/*", "*").exists(t.startsWith)
    // The statement holding the call: the nearest `val`/`def` above it, no deeper than its line...
    val from = (k to 0 by -1).find(j => lines(j).trim.nonEmpty && indent(lines(j)) <= indent(lines(k)) && Statement.matches(lines(j))).getOrElse(k)
    // ...to the next line as shallow as it that does not continue it (a closing bracket, a chained call;
    // a comment may sit between chained calls, and the comments before the next statement are not its).
    val to = ((from + 1) until lines.size).find { j =>
      val t = lines(j).trim
      t.nonEmpty && !comment(t) && indent(lines(j)) <= indent(lines(from)) && !Seq(")", "}", "]", ".").exists(t.startsWith)
    }.getOrElse(lines.size)
    val body = lines.slice(from, to).map(_.stripTrailing).reverse.dropWhile(l => l.isEmpty || comment(l.trim)).reverse
    // Dedented: moving the statement into or out of a block is not a change of what it says.
    val margin = body.filter(_.trim.nonEmpty).map(indent).minOption.getOrElse(0)
    body.map(_.drop(margin)).mkString("\n")
