package frflow.agent

import cats.effect.{ExitCode, IO, Resource}
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.api.{FrFlowApi, Host, Opened}
import frflow.cli.command.{Commands, Dispatch}
import frflow.cli.term.Style
import frflow.cli.{Launch, Scripted}
import frflow.decision.rules.Command as Decide
import java.nio.file.{Files, Path}

/** The agent layer as a project's main object passes it (`Agent`): its records in the project's `.frflow/`, a temporary
  * directory here, over the API in memory.
  */
class AgentLiveSuite extends munit.CatsEffectSuite:
  private val temp = ResourceFunFixture(Resource.make(IO.blocking(Files.createTempDirectory("frflow-agent-live")))(d =>
    IO.blocking(Files.walk(d).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p)))))

  private def run(api: FrFlowApi[IO], host: Host[IO], t: Scripted, args: String*): IO[ExitCode] =
    Sub("frflow", "")(Commands.all(List(Agent))).parse(args.toList, Map.empty) match
      case Right((c, _)) => Dispatch(api, host, t, Style.plain)(List(Agent))(c).handleErrorWith(Launch.failed(t, _))
      case Left(help)    => IO(fail(help.toString))

  temp.test("the developer asks; the agent answers the request; a rejected node is the agent's to replace") { d =>
    val reject = Decide.Reject(frflow.core.name.NodeId("nonNegative"), "a bound says more than a sign here", None)
    for
      api   <- Opened.api(Opened.before)
      host   = Host.of(api, d, Map.empty)
      t     <- Scripted(Nil, interactive = false)
      asked <- run(api, host, t, "ask", "nonNegative", "name the number plainly", "--as", "ann")
      text  <- t.text
      id     = "R[0-9a-z]+".r.findFirstIn(text).getOrElse("R?")
      codes <- List(run(api, host, t, "answer", id, "named it plainly"),
                 api.deciding.decide(reject, "ann").as(ExitCode(0)), run(api, host, t, "inbox")).sequence
      out   <- t.text
      file  <- IO.blocking(Files.readString(d.resolve(".frflow/requests.json")))
    yield
      assertEquals(asked :: codes, List.fill(4)(ExitCode(0)))
      assert(file.contains("named it plainly"), file)
      assert(out.contains("Answers to read (close REQUEST when read)"), out)
      assert(out.contains("nonNegative: rejected by ann: a bound says more than a sign here"), out)
      assert(Files.isRegularFile(Path.of(d.toString, ".frflow", "requests.json")))
  }
