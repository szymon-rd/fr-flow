package frflow.agent
package command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.agent.queue.ForAgent
import frflow.agent.request.{Request, RequestId, RequestStatus}
import frflow.api.{Developer, Host}
import frflow.cli.*
import frflow.protocol.*
import io.circe.syntax.*

/** The agent layer's commands and what it shows in FrFlow's views. */
private[agent] object AgentCommands:
  import Commands.{as, json, layer, node, words}

  private def run(f: (AgentApi, Host, Terminal, Style) => IO[ExitCode]): CliRun = (host, term, st) => Agent.api(host).flatMap(f(_, host, term, st))
  private def done[A](term: Terminal)(lines: A => List[String])(r: Either[AgentRefusal, A]): IO[ExitCode] =
    r.fold(e => term.err(e.message).as(Dispatch.Usage), a => term.out(lines(a)).as(ExitCode.Success))
  private def developer(host: Host, term: Terminal, as: Option[String])(f: Developer => IO[ExitCode]): IO[ExitCode] =
    host.api.developer(as).flatMap(_.fold(r => term.err(r.message).as(Dispatch.Usage), f))

  private def ask(n: Option[NodeId], text: String, as: Option[String]): CliRun = run { (a, host, term, _) =>
    developer(host, term, as)(dev => a.ask(n, text, dev).flatMap(done(term)(q =>
      List(s"asked [${q.id.value}] on ${q.node.fold("the idea")(_.value)}: the agent sees it in its inbox"))))
  }
  private def close(ids: List[String]): CliRun = run { (a, _, term, _) =>
    a.close(ids.map(RequestId(_))).flatMap(done(term)(_.map(r => s"closed [${r.id.value}]")))
  }
  private def conversation(asJson: Boolean): CliRun = run { (a, host, term, st) =>
    host.api.view.flatMap(a.read).flatMap(v =>
      term.out(if asJson then List(Canonical.file(v.conversation.asJson)) else ConversationText.lines(v.conversation, st)).as(ExitCode.Success))
  }
  private def said(text: String): CliRun = run((a, _, term, _) => a.said(text).flatMap(done(term)(_ => List("recorded what the developer said"))))
  private def asked(q: String, assumed: String): CliRun = run { (a, _, term, _) =>
    a.asked(q, assumed).flatMap(done(term)(x => List(s"recorded [${x.id}]: ask it in chat, with the answer you assume")))
  }
  private def replied(q: String, text: String): CliRun = run { (a, _, term, _) =>
    a.replied(q, text).flatMap(done(term)(x => List(s"recorded the reply to [${x.id}]")))
  }
  private def context(id: NodeId): CliRun = (host, term, st) =>
    Dispatch(host.api, term, st, List(Agent), Some(host))(Command.Show(id, Depth.Full, json = false))
      .flatTap(code => if code == ExitCode.Success then term.out("" :: Footer) else IO.unit)
  private def answer(to: String, text: String): CliRun = run { (a, _, term, _) =>
    a.answer(to, text).flatMap(done(term)(id => List(s"answered ${id.value}")))
  }

  private val onIdea = Opts.flag("idea", "about the whole idea, not one node").map(_ => Option.empty[NodeId]).orElse(node().map(Some(_)))
  private val assume = Opts.option[String]("assume", "the answer you assume, which the developer can just confirm")

  val all: List[Sub[(Command, Boolean)]] = List(
    layer("ask", "ask the agent for a change on NODE (or, with --idea, about the whole idea)")((onIdea, words("TEXT"), as).mapN(ask)),
    layer("close", "close requests: an answer read, or a request withdrawn")(Opts.arguments[String]("REQUEST").map(rs => close(rs.toList))),
    layer("conversation", "what you told the agent and its questions, with the answers it assumed and yours: what IDEA.md comes from")(
      json.map(conversation)),
    layer("said", "record what the developer said in chat, word for word (the idea, a correction)")(words("TEXT").map(said)),
    layer("asked", "record a question asked in chat, with the answer you assume (--assume): numbered Q1, Q2, ...")(
      (words("QUESTION"), assume).mapN(asked)),
    layer("replied", "record the developer's reply to a question, as they said it in chat")((Opts.argument[String]("Q"), words("TEXT")).mapN(replied)),
    layer("context", "show --full: everything needed to work on NODE, with the idea and what it rests on, and its requests")(node().map(context)),
    layer("answer", "reply to the developer's request; with a NODE instead, tell them about work they did not ask for")(
      (Opts.argument[String]("REQUEST|NODE"), words("TEXT")).mapN(answer)))

  private val Footer = List("A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.",
    "The developer decides; you propose. The rules are in the frflow skill (.claude/skills/frflow/SKILL.md).")

  /** What the layer adds to FrFlow's views. */
  def contribution(host: Host)(a: AgentView): Contribution =
    val withAgent = a.view.nodes.filter(a.withAgent)
    def on(q: Request) = q.node.fold("the idea")(_.value)
    Contribution(
      aside = a.held,
      marks = withAgent.map(_.id -> "asked").toMap,
      warnings = a.warnings,
      waiting = st => {
        def some(n: Int, what: String, tone: String => String = identity) = Option.when(n > 0)(tone(s"$n $what"))
        List(some(a.conversation.unanswered.size, "question(s) for the developer to answer in chat", st.yellow),
          some(withAgent.size, "asked of the agent", st.magenta), some(a.forAgent.size, "for the agent", st.magenta),
          some(a.open.size, "open request(s)"), some(a.answers.size, "answer(s) to read")).flatten
      },
      inbox = st => {
        import Lines.section
        section("Questions the agent asked: answer them in chat", a.conversation.unanswered.flatMap(q =>
          Lines.para(s"[${q.id}] ${q.text}", st) ++ Lines.para(st.dim(s"assumed: ${q.assumed}"), st, indent = 4).map("  " + _)), st) ++
          section("Requests from the developer", a.open.map(q => s"[${q.id.value}] on ${on(q)} ${st.dot} ${q.by}: ${q.text}"), st) ++
          section("Answers to read (close REQUEST when read)", a.answers.flatMap(q =>
            s"[${q.id.value}] on ${on(q)}: ${q.text}" :: q.answer.toList.map(x => s"  ${st.cyan("agent:")} $x")), st) ++
          section("With the agent: asked, until it answers or changes the node", withAgent.map(Lines.node(_, st, 4)), st) ++
          section("For the agent", a.forAgent.flatMap(t => Lines.para(task(t, st), st)), st)
      },
      node = (id, st) => Lines.section("Requests", a.requests.filter(q => q.node.contains(id) && q.status != RequestStatus.Closed)
        .flatMap(q => s"[${q.id.value}] ${q.status} ${st.dot} ${q.by}: ${q.text}" :: q.answer.filter(_.nonEmpty).map(x => s"  agent: $x").toList), st),
      review = List(ReviewKey("?", "[?]ask", (dev, r, term, st) => term.read("What should change? ").flatMap {
        case Some(text) if text.trim.nonEmpty => Agent.api(host).flatMap(_.ask(Some(r.id), text, dev)).flatMap {
          case Left(e) => term.out(st.red(s"refused: ${e.message}"))
          case Right(q) => term.out(List(s"asked [${q.id.value}]: ${r.id} is with the agent until it answers or changes it"))
        }
        case _ => IO.unit
      })))

  private def task(t: ForAgent, st: Style): String = t match
    case ForAgent.Replace(node, by, reason) =>
      s"${st.bold(node.value)}: ${st.red(s"rejected by $by")}: ${reason.trim.stripSuffix(".")}; " +
        "propose what the reason asks for in its place, or remove it from the Scala model"
    case ForAgent.Revisit(node, reason) =>
      s"${st.bold(node.value)}: ${st.yellow("the developer asked to revisit it")} ($reason): propose a change, or `answer $node TEXT` why it still holds"
    case ForAgent.Move(node, parents) => s"${st.bold(node.value)}: rests on rejected ${parents.mkString(", ")}; move it under the node chosen instead"
