package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** What changed since a node was decided, as lines: each field as a compact line diff, the parts added
  * or removed, what moved above it, a rejected parent, a revisit asked, the code's git diff.
  */
object DiffText:
  def lines(d: NodeDiff, st: Style): List[String] =
    val since = d.since.fold("since it was decided")(x => s"since it was ${Words.verb(x.action)} (${x.by}, ${Words.date(x.at)})")
    val parts = List(
      Option.when(d.partsAdded.nonEmpty)(s"parts added: ${d.partsAdded.mkString(", ")}"),
      Option.when(d.partsRemoved.nonEmpty)(s"parts removed: ${d.partsRemoved.mkString(", ")}")).flatten
    val body =
      fields(d.self, st) ++
        Option.when(d.statementStale)(st.yellow("! what it says formally changed and its statement did not: does the statement still say it?")) ++
        parts.map(p => s"${st.yellow(p)}: do these parts, together, still make it?") ++
        d.moved.flatMap { m =>
          val how = if m.acceptedAgain then st.green(s"you accepted that${m.reason.fold("")(r => s": $r")}") else st.yellow("not accepted yet")
          s"the meaning of ${st.bold(m.id.value)} changed (${how})" :: fields(m.changes, st).map("  " + _)
        } ++
        d.rejectedParents.map(p => st.red(s"its parent $p was rejected: the agent moves it under the node chosen instead")) ++
        d.revisit.map(r => st.yellow(s"${r.by} asked to revisit it: ${r.reason}")) ++
        d.code.toList.flatMap(code(_, st))
    if body.isEmpty then List(st.dim(s"Nothing changed $since."))
    else st.heading(s"What changed $since") :: body.map("  " + _)

  def fields(fs: List[FieldChange], st: Style): List[String] =
    fs.flatMap(f => st.bold(f.field) :: f.lines.map(l => "  " + line(l, st)))

  private def line(l: DiffLine, st: Style): String = l.op match
    case DiffOp.Same    => st.dim(s"  ${l.text}")
    case DiffOp.Added   => st.green(s"+ ${l.text}")
    case DiffOp.Removed => st.red(s"- ${l.text}")
    case DiffOp.Folded  => st.dim(s"${st.ellipsis} ${l.text} unchanged line(s)")

  def code(c: CodeChange, st: Style): List[String] =
    val what = if c.inFull then s"the files it governs, in full: read them before accepting (${c.files.mkString(", ")})"
      else s"the code it governs changed (${c.files.mkString(", ")})"
    val text = c.text.linesIterator.toList
    st.bold(what) :: (if text.isEmpty then List(st.dim("  no git diff available (decided outside git, or before the code was committed)"))
      else text.map { l =>
        if c.inFull then "  " + l
        else if l.startsWith("+") && !l.startsWith("+++") then "  " + st.green(l)
        else if l.startsWith("-") && !l.startsWith("---") then "  " + st.red(l)
        else if l.startsWith("@@") then "  " + st.cyan(l)
        else "  " + st.dim(l)
      })

/** Words shared by the views. */
object Words:
  def verb(a: Action): String = a match
    case Action.Accept  => "accepted"
    case Action.Confirm => "confirmed"
    case Action.Reject  => "rejected"
    case Action.Revisit => "asked to revisit"
    case Action.Remove  => "agreed gone"

  /** An instant as people read it: `2026-10-23 01:42`. */
  def date(at: String): String = at.take(16).replace('T', ' ')

  val causes: Map[Cause, String] = Map(
    Cause.Self -> "it changed",
    Cause.Above -> "the meaning of what it rests on changed",
    Cause.Parts -> "its parts changed",
    Cause.Code -> "the code it governs changed",
    Cause.Revisit -> "a change elsewhere may affect it",
    Cause.Merged -> "two branches decided it and both were kept")

  def decided(l: Logged): String =
    val d = l.decision
    s"${d.action} ${l.node}${if d.rejected.isEmpty then "" else s", rejecting ${d.rejected.mkString(", ")}"}"
