package frflow.agent

import cats.effect.IO
import com.monovore.decline.Command as Sub
import frflow.agent.command.{AgentCommands, AgentText, AskKey}
import frflow.agent.panel.AgentWeb
import frflow.agent.work.AgentApi
import frflow.api.Host
import frflow.api.view.View
import frflow.cli.command.{CliExtension, Command}
import frflow.cli.review.ReviewKey
import frflow.cli.term.Style
import frflow.cli.text.Contribution
import frflow.web.{WebExtension, WebPart}

/** The AI agent's layer on top of FrFlow, over the agent layer's API `open` gives for a project: on the command line
  * its commands, what it adds to FrFlow's views and `[?]` in the review; in the web view its routes and panels. It
  * proposes and asks; deciding stays the developer's, with their key.
  */
class AgentLayer(open: Host[IO] => IO[AgentApi[IO]]) extends CliExtension with WebExtension:
  override val header: String =
    """With an AI agent (frflow.agent): the developer tells the agent the idea in chat; the agent records the
      |conversation (said, asked, replied; read it with conversation) and proposes the root statements and their parts
      |in the model, its rationale in the conversation or an answer, never in a node. The developer asks for changes
      |with ask (or [?] in review) and closes requests with close; the agent works with context and answer. Only the
      |developer decides.""".stripMargin

  def commands: List[Sub[(Command, Boolean)]] = AgentCommands(open, this).all

  def contribute(host: Host[IO], v: View, st: Style): IO[Contribution] =
    open(host).flatMap(_.read(v)).map(AgentText.contribution(_, st))

  def keys(host: Host[IO]): List[ReviewKey] = List(AskKey(open(host)))

  def part(host: Host[IO], developer: String): IO[WebPart] = open(host).flatMap(AgentWeb.part(host, developer, _))
