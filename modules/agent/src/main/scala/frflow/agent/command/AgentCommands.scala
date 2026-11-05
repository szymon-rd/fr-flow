package frflow.agent.command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.agent.request.{AgentRefusal, RequestId}
import frflow.agent.work.AgentApi
import frflow.api.Host
import frflow.cli.command.Options.{as, node, words}
import frflow.cli.command.{CliExtension, Command, Commands}
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.{Depth, NodeText}
import frflow.core.name.NodeId
import io.circe.syntax.*

/** The agent layer's commands: the developer asks and closes (`ask`, `close`); the agent records the conversation
  * (`said`, `asked`, `replied`), reads what it needs (`context`, `conversation`) and answers (`answer`). None decides.
  * `open` gives the layer's API over a project; `layer` is the layer itself, whose view `context` shows.
  */
final class AgentCommands(open: Host[IO] => IO[AgentApi[IO]], layer: CliExtension):
  private type Run = (Host[IO], Terminal, Style) => IO[ExitCode]

  private def run(f: (AgentApi[IO], Host[IO], Terminal, Style) => IO[ExitCode]): Run =
    (host, term, st) => open(host).flatMap(f(_, host, term, st))

  private def done[A](term: Terminal)(lines: A => List[String])(r: Either[AgentRefusal, A]): IO[ExitCode] =
    r.fold(e => term.err(e.message).as(Exit.Usage), a => term.out(lines(a)).as(Exit.Fine))

  private def ask(n: Option[NodeId], text: String, who: Option[String]): Run = run { (a, host, term, _) =>
    host.developer(who).flatMap(_.fold(_ => term.err("who asks? pass --as NAME").as(Exit.Usage), by =>
      a.ask(n, text, by).flatMap(done(term)(q => List(s"asked [${q.id.value}] on ${q.node.fold("the idea")(_.value)}" +
        ": the agent sees it in its inbox")))))
  }

  /** `show --full` of the node, with what the layer adds, then what the agent works by. */
  private def context(id: NodeId): Run = (host, term, st) =>
    host.reading.view.flatMap(v => layer.contribute(host, v, st).flatMap(x => v.node(id).fold(
      term.err(s"unknown node $id").as(Exit.Usage))(n =>
        term.out(NodeText(v, st, x).lines(n, Depth.Full) ++ ("" :: AgentCommands.Footer)).as(Exit.Fine))))

  private val onIdea = Opts.flag("idea", "about the whole idea, not one node").as(Option.empty[NodeId])
    .orElse(node().map(Some(_)))

  val all: List[Sub[(Command, Boolean)]] = List(
    Commands.layer("ask", "ask the agent for a change on NODE (or, with --idea, about the whole idea)")(
      (onIdea, words("TEXT"), as).mapN(ask)),
    Commands.layer("close", "close requests: an answer read, or a request withdrawn")(
      Opts.arguments[String]("REQUEST").map(rs => run((a, _, term, _) =>
        a.close(rs.toList.map(RequestId(_))).flatMap(done(term)(_.map(r => s"closed [${r.id.value}]")))))),
    Commands.layer("conversation", "what you told the agent and its questions, with the answers it assumed and yours")(
      Opts.flag("json", "the record as JSON").orFalse.map(json => run((a, host, term, st) => host.reading.view
        .flatMap(a.read).flatMap(v => term.out(if json then List(v.conversation.asJson.spaces2)
          else AgentText.conversation(v.conversation, st)).as(Exit.Fine))))),
    Commands.layer("said", "record what the developer said in chat, word for word")(words("TEXT").map(t =>
      run((a, _, term, _) => a.said(t).flatMap(done(term)(_ => List("recorded what the developer said")))))),
    Commands.layer("asked", "record a question asked in chat, with the answer you assume (--assume)")(
      (words("QUESTION"), Opts.option[String]("assume", "the answer you assume, which the developer can just confirm"))
        .mapN((q, assumed) => run((a, _, term, _) => a.asked(q, assumed).flatMap(done(term)(x =>
          List(s"recorded [${x.id}]: ask it in chat, with the answer you assume")))))),
    Commands.layer("replied", "record the developer's reply to a question, as they said it in chat")(
      (Opts.argument[String]("QUESTION"), words("TEXT")).mapN((q, t) => run((a, _, term, _) =>
        a.replied(q, t).flatMap(done(term)(x => List(s"recorded the reply to [${x.id}]")))))),
    Commands.layer("context", "show --full: everything needed to work on NODE, with its requests")(
      node().map(context)),
    Commands.layer("answer", "reply to the developer's request; with a NODE instead, tell them of work they did not " +
      "ask for")((Opts.argument[String]("REQUEST|NODE"), words("TEXT")).mapN((to, t) => run((a, _, term, _) =>
        a.answer(to, t).flatMap(done(term)(id => List(s"answered ${id.value}")))))))

object AgentCommands:
  val Footer: List[String] = List(
    "A new statement belongs under the lowest nodes it helps prove, as a part; never as a restatement of a node.",
    "The developer decides; you propose, with your rationale in an answer or the conversation, never in the node.")
