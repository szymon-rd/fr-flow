package frflow.cli.text

import frflow.api.view.diff.{DiffLine, FieldDiff, NodeDiff}
import frflow.cli.term.Style
import frflow.core.name.NodeId

/** What moved under a node's decision (`diff`): its fields, what it rests on, its parts, its code. Long unchanged runs
  * are folded to their first and last lines.
  */
object DiffText:
  private val Kept = 2

  def lines(id: NodeId, d: Option[NodeDiff], decided: Boolean, st: Style): List[String] = d match
    case None                 => List(s"unknown node $id")
    case Some(_) if !decided  => List(s"$id is not decided yet: everything in it is new (show $id reads it)")
    case Some(x) if empty(x)  => List(s"nothing moved under $id since it was decided")
    case Some(x)              => x.fields.flatMap(field(_, st)) ++ x.above.flatMap(m =>
        Lines.section(s"${m.id} moved above it since:", m.fields.flatMap(field(_, st)), st)) ++
      Lines.section("Parts", x.parts.added.map(p => st.green(s"+ $p")) ++ x.parts.removed.map(p => st.red(s"- $p")),
        st) ++ Lines.section("Code since the decision's commit", x.code.toList.flatMap(code(_, st)), st)

  private def empty(d: NodeDiff): Boolean =
    d.fields.isEmpty && d.above.isEmpty && d.parts.added.isEmpty && d.parts.removed.isEmpty && d.code.isEmpty

  def field(f: FieldDiff, st: Style): List[String] = s"${st.bold(f.field)}:" :: folded(f.lines).map {
    case Some(DiffLine.Same(t))    => s"  $t"
    case Some(DiffLine.Added(t))   => st.green(s"+ $t")
    case Some(DiffLine.Removed(t)) => st.red(s"- $t")
    case None                      => st.dim(s"  ${st.ellipsis}")
  }

  /** Each line, but those of an unchanged run with at least `Kept` unchanged lines on either side: one gap (none)
    * stands for each stretch of them.
    */
  private def folded(ls: List[DiffLine]): List[Option[DiffLine]] =
    val same = ls.map { case DiffLine.Same(_) => true; case _ => false }.toVector
    def run(i: Int, step: Int) = Iterator.iterate(i + step)(_ + step).takeWhile(j => same.lift(j).contains(true)).size
    def hidden(i: Int) = same(i) && run(i, -1) >= Kept && run(i, 1) >= Kept
    ls.zipWithIndex.flatMap((l, i) =>
      if !hidden(i) then List(Some(l)) else if i > 0 && hidden(i - 1) then Nil else List(None))

  private def code(diff: String, st: Style): List[String] = diff.linesIterator.toList.map { l =>
    if l.startsWith("+") && !l.startsWith("+++") then st.green(l)
    else if l.startsWith("-") && !l.startsWith("---") then st.red(l)
    else l
  }
