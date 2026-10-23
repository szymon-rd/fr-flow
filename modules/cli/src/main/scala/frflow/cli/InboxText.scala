package frflow.cli

import frflow.api.*
import frflow.ledger.ForAgent
import frflow.protocol.*

/** What waits for whom: the developer's requests and the answers, warnings, decisions to sign, the
  * developer's queue, what is with the agent and the agent's tasks; then the tree. One view for both.
  */
object InboxText:
  import Lines.section

  def lines(i: Inbox, tree: Tree, st: Style): List[String] =
    def on(q: Request) = q.node.fold("the idea")(_.value)
    def waiting(w: Queued) =
      Lines.node(w.node, st, 4, w.waitsFor.fold("")(x => st.dim(s"  after $x"))) ::
        w.followers.map(f => st.dim(s"  ${st.follows} $f moved with it: decided with it (accepting it confirms $f)"))
    val body =
      section("Requests from the developer", i.open.map(q => s"[${q.id}] on ${on(q)} ${st.dot} ${q.by}: ${q.text}"), st) ++
        section("Answers to read (close REQUEST when read)", i.answers.flatMap(q =>
          s"[${q.id}] on ${on(q)}: ${q.text}" :: q.answer.toList.map(a => s"  ${st.cyan("agent:")} $a")), st) ++
        section("Warnings: status fails on each", i.warnings.map(w => st.red(s"${st.bullet} $w")), st) ++
        section("Not signed by a developer key (sign ENTRY…, for the ones that are yours)", i.unsigned.map(u =>
          s"${st.dim(u.entry.value)} ${u.node}: ${u.decision.action} by ${u.decision.by}, ${Words.date(u.decision.at)}: ${u.decision.reason}"), st) ++
        section("For the developer: ready to decide (review, or accept / reject NODE)", i.ready.flatMap(waiting), st) ++
        section(s"Mechanical: Lean proves them again, nothing in them is a choice (confirm decides all ${i.mechanical.size})",
          i.mechanical.map(Lines.node(_, st, 4)), st) ++
        section("After the decisions above them", i.later.flatMap(waiting), st) ++
        section("Gone from the model (gone NODE)", i.gone.map(g => s"${st.bold(g.id.value)}: ${g.decision.content.statement}"), st) ++
        section("Asked of the agent: with the agent until it answers or changes the node", i.withAgent.map(Lines.node(_, st, 4)), st) ++
        section("For the agent", i.forAgent.flatMap(t => Lines.para(task(t, st), st)), st)
    val nothing = if body.nonEmpty then Nil else List(st.green("Nothing waits: no request, no decision, nothing for the agent."))
    (body ++ nothing).dropWhile(_.isEmpty) ++ ("" :: st.heading("The tree") :: TreeText.lines(tree, st))

  def task(t: ForAgent, st: Style): String = t match
    case ForAgent.Replace(node, by, reason) =>
      s"${st.bold(node.value)}: ${st.red(s"rejected by $by")}: ${reason.trim.stripSuffix(".")}; " +
        "propose what the reason asks for in its place, or remove it from the Scala model"
    case ForAgent.Revisit(node, reason) =>
      s"${st.bold(node.value)}: ${st.yellow("the developer asked to revisit it")} ($reason): propose a change, or `answer $node TEXT` why it still holds"
    case ForAgent.Move(node, parents) =>
      s"${st.bold(node.value)}: rests on rejected ${parents.mkString(", ")}; move it under the node chosen instead"
