package frflow.agent.command

import frflow.agent.conversation.Conversation
import frflow.agent.request.Request
import frflow.agent.work.{AgentView, ForAgent}
import frflow.cli.term.Style
import frflow.cli.text.{Contribution, Lines}

/** What the agent layer shows in FrFlow's views (a node with the agent held back from the queue and marked, what waits
  * for the agent and for the developer), and the conversation as `conversation` prints it.
  */
object AgentText:
  def contribution(a: AgentView, st: Style): Contribution =
    val withAgent = a.view.nodes.filter(a.withAgent)
    def some(n: Int, what: String, tone: String => String) = Option.when(n > 0)(tone(s"$n $what"))
    Contribution(a.held, withAgent.map(_.id -> "asked").toMap, Nil,
      List(some(a.conversation.unanswered.size, "question(s) to answer in chat", st.yellow),
        some(withAgent.size, "asked of the agent", st.magenta), some(a.forAgent.size, "for the agent", st.magenta),
        some(a.answers.size, "answer(s) to read", identity)).flatten,
      inbox(a, st), id => Lines.section("Requests", a.requests.filter(q => q.node.contains(id) &&
        q.status != frflow.agent.request.RequestStatus.Closed).flatMap(request(_, st)), st))

  private def inbox(a: AgentView, st: Style): List[(String, List[String])] = List(
    "Questions the agent asked: answer them in chat" -> a.conversation.unanswered.flatMap(q =>
      s"[${q.id}] ${q.text}" :: List(st.dim(s"  assumed: ${q.assumed}"))),
    "Requests from the developer" -> a.open.map(q => s"[${q.id.value}] on ${on(q)} ${st.dot} ${q.asked.by}: ${q.text}"),
    "Answers to read (close REQUEST when read)" -> a.answers.flatMap(request(_, st)),
    "With the agent: asked, until it answers or changes the node" ->
      a.view.nodes.filter(a.withAgent).map(Lines.node(_, st, 4)),
    "For the agent" -> a.forAgent.map(task(_, st)))

  private def on(q: Request): String = q.node.fold("the idea")(_.value)

  private def request(q: Request, st: Style): List[String] =
    s"[${q.id.value}] on ${on(q)} ${st.dot} ${q.status.word} ${st.dot} ${q.asked.by}: ${q.text}" ::
      q.answer.toList.map(x => s"  ${st.cyan("agent:")} ${x.text}")

  def task(t: ForAgent, st: Style): String = t match
    case ForAgent.Replace(node, by, reason) => s"${st.bold(node.value)}: ${st.red(s"rejected by $by")}: " +
        s"${reason.trim.stripSuffix(".")}; propose what the reason asks for in its place, or remove it from the model"
    case ForAgent.Revisit(node, reason)     => s"${st.bold(node.value)}: ${st.yellow("the developer asked to " +
        s"revisit it")} ($reason): propose a change, or `answer $node TEXT` why it still holds"
    case ForAgent.Move(node, parents)       => s"${st.bold(node.value)}: rests on rejected ${parents.mkString(", ")};" +
        " move it under the node chosen instead"

  def conversation(c: Conversation, st: Style): List[String] =
    if c.said.isEmpty && c.questions.isEmpty then List("Nothing recorded yet: tell the agent your idea in chat.")
    else (Lines.section("What you said", c.said.map(_.text), st) ++
      Lines.section("What the agent asked", c.questions.flatMap(q => s"[${q.id}] ${q.text}" ::
        st.dim(s"  assumed: ${q.assumed}") :: q.replies.dropRight(1).map(r => st.dim(s"  earlier: ${r.text}")) ++
        List(q.answer.fold(st.yellow("  no reply yet"))(x => s"  ${st.cyan("you:")} $x"))), st)).drop(1)
