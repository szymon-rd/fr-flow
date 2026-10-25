package frflow.agent

import cats.effect.IO
import com.monovore.decline.Command as Sub
import frflow.agent.command.AgentCommands
import frflow.agent.panel.AgentWeb
import frflow.api.{Developer, Host, View}
import frflow.cli.*
import frflow.web.{WebExtension, WebPart}
import java.nio.file.Path
import java.util.concurrent.ConcurrentHashMap

/** The AI agent's layer on top of FrFlow, as a project's main object passes it:
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth", extensions = List(frflow.agent.Agent))
  * }}}
  * It adds the conversation a project starts from (`said`, `asked`, `replied`, `conversation`), the developer's requests
  * and the agent's answers (`ask`, `close`, `answer`, and `?` in the review), the agent's queue, and `context`; and the
  * same in the web view. Its files are `.frflow/requests.json` and `.frflow/conversation.json`; FrFlow never reads them.
  */
object Agent extends CliExtension with WebExtension:
  // One per project directory in a process: its files' locks are shared (see `FileLock`).
  private val opened = ConcurrentHashMap[Path, AgentApi]()
  def api(host: Host): IO[AgentApi] =
    IO(Option(opened.get(host.directory))).flatMap(_.fold(AgentApi.live(host).map(a => Option(opened.putIfAbsent(host.directory, a)).getOrElse(a)))(IO.pure))

  override val header: String =
    """With an AI agent (frflow.agent): the developer tells the agent the idea in chat; the agent records the conversation
      |(said, asked, replied; read it with conversation) and writes IDEA.md from it. The developer asks for changes with ask
      |(or [?] in review) and closes requests with close; the agent works with context and answer.""".stripMargin

  def commands: List[Sub[(Command, Boolean)]] = AgentCommands.all
  override def contribute(host: Host, v: View): IO[Contribution] = api(host).flatMap(_.read(v)).map(AgentCommands.contribution(host))
  def part(host: Host, dev: Developer): IO[WebPart] = api(host).flatMap(AgentWeb.part(host, dev, _))
