package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** What changed since a node was decided, as lines wrapped to the width less 2 (room for a caller's indent). */
object DiffText:
  def lines(d: NodeDiff, st: Style): List[String] = unwrapped(d, st).flatMap(st.fold(_, 2))

  private def unwrapped(d: NodeDiff, st: Style): List[String] =
    val parts = List(Option.when(d.partsAdded.nonEmpty)(s"parts added: ${d.partsAdded.mkString(", ")}"),
      Option.when(d.partsRemoved.nonEmpty)(s"parts removed: ${d.partsRemoved.mkString(", ")}")).flatten
    val codeLines = d.code.toList.flatMap(code(_, st))
    val body = fields(d.self, st) ++
        Option.when(d.statementStale)(st.yellow("! what it says formally changed and its statement did not: does the statement still say it?")) ++
        parts.map(p => s"${st.yellow(p)}: do these parts, together, still make it?") ++
        d.moved.flatMap { m =>
          val how = if m.acceptedAgain then st.green(s"you accepted that${m.reason.fold("")(r => s": $r")}") else st.yellow("not accepted yet")
          s"the meaning of ${st.bold(m.id.value)} changed (${how})" :: fields(m.changes, st).map("  " + _)
        } ++
        d.rejectedParents.map(p => st.red(s"its parent $p was rejected: move it under the node chosen instead")) ++
        d.revisit.map(r => st.yellow(s"${r.by} asked to revisit it: ${r.reason}")) ++ codeLines
    d.since match
      case None => st.bold("New: never decided") :: codeLines.map("  " + _)
      case Some(x) =>
        // A confirmation accepts the node with what moved it: said as accepted, as the decision it confirms is.
        val verb = if x.action == Action.Confirm then Words.verb(Action.Accept) else Words.verb(x.action)
        val since = s"since it was $verb (${x.by}, ${Words.date(x.at)})"
        if body.isEmpty then List(st.dim(s"Nothing changed $since."))
        else st.bold(s"What changed $since") :: body.map("  " + _)

  private def fields(fs: List[FieldChange], st: Style): List[String] =
    fs.flatMap(f => st.bold(f.field) :: f.lines.map {
      case DiffLine.Same(t)    => "  " + st.dim(s"  $t")
      case DiffLine.Added(t)   => "  " + st.green(s"+ $t")
      case DiffLine.Removed(t) => "  " + st.red(s"- $t")
      case DiffLine.Folded(n)  => "  " + st.dim(s"${st.ellipsis} $n unchanged line(s)")
    })

  private def code(c: CodeChange, st: Style): List[String] =
    val text = c.text.linesIterator.toList
    val title = if c.inFull then s"the files it governs, in full: read them before accepting (${c.files.mkString(", ")})"
      else s"the code it governs changed (${c.files.mkString(", ")})"
    st.bold(title) :: (if text.isEmpty then List(st.dim("  no git diff available (decided outside git, or before the code was committed)"))
      else text.map { l =>
        if c.inFull then "  " + l
        else if l.startsWith("+") && !l.startsWith("+++") then "  " + st.green(l)
        else if l.startsWith("-") && !l.startsWith("---") then "  " + st.red(l)
        else if l.startsWith("@@") then "  " + st.cyan(l)
        else "  " + st.dim(l)
      })
