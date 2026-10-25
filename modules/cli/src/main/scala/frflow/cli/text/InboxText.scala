package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** What waits for the developer; then what layers on top add (`c`); the summary last. */
object InboxText:
  import Lines.section

  /** `v`: the view the inbox was read from, for a gone node renamed. */
  def lines(i: Inbox, v: View, st: Style, c: Contribution = Contribution.empty): List[String] =
    def waiting(w: Queued) =
      Lines.node(w.node, st, 4, w.waitsFor.fold("")(x => st.dim(s"  after $x"))) ::
        w.followers.map(f => st.dim("  " + Words.follower(f, w.node.id, st)))
    val idea = i.idea.toList.flatMap { r =>
      val how = if r.state == ReviewState.Review then "changed since you accepted it" else "not accepted yet"
      Lines.para(s"${st.bold("IDEA")}  ${st.yellow(s"IDEA.md, $how")}: read it, then accept IDEA (the root is decided after it)", st)
    }
    val body =
      section("IDEA.md, first", idea, st) ++
        section("Warnings: status fails on each", (i.warnings ++ c.warnings).map(w => st.red(s"${st.bullet} $w")), st) ++
        section("For the developer, in order (review, or accept / reject NODE)", i.queue.flatMap(waiting), st) ++
        section(s"Mechanical: Lean proves them again, nothing in them is a choice (confirm decides all ${i.mechanical.size})",
          i.mechanical.map(Lines.node(_, st, 4)), st) ++
        section("Gone from the model (gone NODE)", i.gone.map(Details.gone(v, _)).map(g => st.fit(s"${st.bold(g.gone.id.value)}" +
          s"${g.renamedTo.fold("")(y => st.yellow(s"  renamed to $y"))}: ${g.gone.decision.content.statement}", 2)), st) ++
        c.inbox(st)
    (body ++ ("" :: SummaryText.lines(i.overview, st, c.waiting(st)))).dropWhile(_.isEmpty)
