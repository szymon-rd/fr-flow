package frflow
package check
package analysis

import frflow.ledger.*
import frflow.protocol.*
import io.circe.Json

/** A node as the developer sees it and decides it: a decision is bound to its hash, its parts too (docs/DAG.md §5). */
object Contents:
  private def str(s: String): Json = Json.fromString(s)
  private def strs(xs: Seq[String]): Json = Json.fromValues(xs.map(Json.fromString))

  def of(a: Analysis, n: Node[?]): Content =
    val kb = a.kb
    val implementation = kb.implementation(n).flatMap { i =>
      // A flow is decided as Lean reads it: its Scala is a `def` elsewhere, governed by a design decision.
      val proven = i.proven.toList.flatMap(d => s"proven: ${d.name}" +: Def.closure(List(d))
        .map(x => s"${x.name} = ${if x.isFlow then x.lifted.lean else x.lifted.source}"))
      val runs = Option.when(i.wiring.nonEmpty)(if i.proven.isDefined then s"runs: ${i.wiring}" else i.wiring).toList
      Option.when((proven ++ runs).nonEmpty)((proven ++ runs).mkString("\n"))
    }
    // The root is decided against the idea's title and lead; a node naming a section, against that section.
    val idea =
      if n.ideaSection.nonEmpty then Seq("idea" -> str(a.ideaOf(n)), "ideaSection" -> str(n.ideaSection), "notModelled" -> str(a.notModelled))
      else if kb.isRoot(n) then Seq("idea" -> str(Idea.sections(a.ideaDecided)._1), "notModelled" -> str(a.notModelled))
      else Nil
    val terms = kb.termsOf(n).toSet ++ n.defines
    val vocabulary = (kb.opaques.filter(o => terms(o.name)).map(o => s"${o.name}: ${o.means}") ++
      kb.params.filter(p => terms(p.name)).map(p => s"${p.name}: ${p.means}")).sorted
    val sources = Seq("formula" -> n.formula, "post" -> n.post, "rule" -> n.rule, "check" -> n.local)
      .collect { case (k, Some(l)) => k -> str(l.source) }
    // The fields in this order: the order is part of the hash, so a change of it reviews every node again.
    Content((List(
      Some("kind" -> str(n.kind.toString)),
      Some("parents" -> strs(n.parents.map(_.id))),
      Option.when(kb.isStatement(n))("parts" -> strs(kb.parts(n).map(_.id))),
      Some("statement" -> str(n.statement)),
      Some("why" -> str(n.why)),
      Some("sources" -> Json.obj(sources*)),
      Some("substitutions" -> strs(n.substs.map(s => s"${s.name} := ${s.term.fold(s.lean)(_.source)}"))),
      Some("examples" -> strs(n.cases.map(_.describe))),
      Some("vocabulary" -> strs(vocabulary)),
      Some("uses" -> strs(a.generate.sourcesUsedBy(n))),
      Some("governs" -> strs(n.governs)),
      Some("definition" -> str(a.definition(n))),
      n.op.map(o => "op" -> str(o.name)),
      n.replaced.map(r => "replaces" -> str(r.id)),
      Option.when(n.kept.nonEmpty)("keeps" -> strs(n.kept.map(_.describe))),
      Option.when(n.expected.nonEmpty)("expects" -> strs(n.expected.map((st, l) => s"$st: ${l.source}"))),
      implementation.map("implementation" -> str(_)),
      n.modelOf.map(mo => "model" -> strs(a.generate.boundaryModules.modelText(mo))),
      n.modelOf.filter(_.impls.nonEmpty).map(mo => "implementations" -> strs(mo.impls.map(i =>
        s"${if i.outside then CodeProof.Outside else CodeProof.Own}${i.source}"))),
      // Only a choice is decided: the default follows from the implementation, which is decided above.
      n.runCheck.map(c => "runtime" -> str(c.describe))
    ).flatten ++ idea)*)

  private val Statement = """^\s*(?:(?:private|protected|final|lazy|override|inline)\s+)*(?:val|def|given|var)\b.*""".r

  /** The top-level definition at `at`, with every call chained on it: the text the developer decides. */
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
