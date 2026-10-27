package frflow.cli.text

import frflow.api.view.{Overview, Piece, View}
import frflow.api.view.whole.GroupStatus
import frflow.cli.term.{Marks, Style}
import frflow.decision.review.ReviewState

/** The lines every view closes with: the counts by concept, what waits, the legend; `more`, what layers on top add to
  * what waits.
  */
object SummaryText:
  def lines(v: View, waiting: Int, st: Style, more: List[String] = Nil): List[String] =
    val o = v.overview
    val sep = if st.unicode then s" ${st.dot} " else ", "
    val head = s"${st.bold("FrModel")}: ${v.nodes.size} nodes$sep${counts(o, st).mkString(sep)}"
    val waits = Option.when(waiting > 0)(st.yellow(s"$waiting for the developer")).toList ++ more
    val last = if waits.nonEmpty then s"Waiting: ${waits.mkString(sep)}"
      else if o.complete then st.green("Nothing waits: every node is accepted and proven, or its code tested.")
      else "Nothing waits for a decision."
    if v.nodes.isEmpty then List(s"${st.bold("FrModel")}: no nodes yet: propose the root statements first")
    else (head :: List(proofs(o, st), tests(o, st)).flatten) ++ List(last, Marks.legend(st))

  private def counts(o: Overview, st: Style): List[String] =
    def some(n: Int, what: String, tone: String => String) = Option.when(n > 0)(tone(s"$n $what"))
    (Some(st.green(s"${o.review(ReviewState.Accepted)} accepted")) :: List(
      some(o.review(ReviewState.Review), "to review", st.yellow), some(o.review(ReviewState.Proposed), "proposed",
        st.cyan), some(o.review(ReviewState.Rejected), "rejected", st.red))).flatten

  private def proofs(o: Overview, st: Style): Option[String] =
    val groups = o.consistency
    val all = groups.counts.values.sum
    val consistency = if all == 0 then None
      else if groups(GroupStatus.Proven) == all then Some(st.green("consistency proven"))
      else Some(st.red(s"consistency not proven (${all - groups(GroupStatus.Proven)} of $all group(s))"))
    val code = List(Piece.Proven -> "proven", Piece.Tested -> "tested", Piece.Assumed -> "assumed")
      .collect { case (p, w) if o.code(p) > 0 => s"${o.code(p)} $w" }
    Option.when(code.nonEmpty || consistency.isDefined)(
      ("Code: " + (if code.isEmpty then "none" else code.mkString(", "))) + consistency.fold("")(c => s"; $c"))

  private def tests(o: Overview, st: Style): Option[String] =
    val (ok, all) = (o.examples(true), o.examples(true) + o.examples(false))
    Option.when(all > 0)(s"Examples: ${if ok == all then st.green(s"$ok/$all pass") else st.red(s"$ok/$all pass")}")
