package frflow
package cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import cats.syntax.all.*
import com.monovore.decline.Command as Sub
import frflow.api.{Extension, FrFlowError, FrFlowProject, Host, LiveApi}
import java.nio.file.Path

/** The command line of a knowledge base, which a project's main object extends:
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth")
  * }}}
  * `root` is the project's directory (`FRFLOW_ROOT` overrides it); `kernelPath`, FrFlow's Lean kernel
  * relative to the project's `lean/`; `extensions`, the layers on top it uses (their commands follow FrFlow's, e.g.
  * `extensions = List(frflow.agent.Agent)` for an AI agent's). A usage error prints the help and exits 2. The web
  * view runs from the same object, through sbt (`sbt "auth/serve --as NAME"`), not from here.
  */
abstract class FrFlowApp(knowledge: => KnowledgeBase, val root: String = ".", val kernelPath: String = "../../../lean",
    override val extensions: List[Extension] = Nil) extends IOApp with FrFlowProject:
  final def kb: KnowledgeBase = knowledge
  private def cli: List[CliExtension] = extensions.collect { case c: CliExtension => c }
  final def run(args: List[String]): IO[ExitCode] = IO(sys.env).flatMap { env =>
    val name = Option(Path.of(root).normalize.getFileName).map(_.toString).filter(n => n.nonEmpty && n != ".").getOrElse("frflow")
    Sub(name, Commands.header(cli))(Commands.all(cli)).parse(args, env) match
      case Right((command, plain)) =>
        for
          term <- Terminal.live
          st = Style.of(plain, env, term.interactive)
          code <- LiveApi.fromEnv(knowledge, root, kernelPath, env)
            .flatMap(api => Dispatch(api, term, st, cli, Some(Host(api, directory(env), env)))(command))
            .handleErrorWith(FrFlowApp.failed(term, _))
        yield code
      case Left(help) =>
        // The commands are listed once, under Subcommands: not again as a usage line each.
        val once = if help.usage.size > 3 then help.copy(usage = List("[--plain] COMMAND [ARGS]...")) else help
        if help.errors.isEmpty then IO.println(once).as(ExitCode.Success) else Console[IO].errorln(once).as(Dispatch.Usage)
  }

object FrFlowApp:
  /** The one place failures become exit codes: the model's problems 1, an unknown node 2, no Lean 3. */
  private[cli] def failed(term: Terminal, e: Throwable): IO[ExitCode] = e match
    case FrFlowError.ModelProblems(ps) => ps.traverse_(p => term.err(s"error: $p")).as(Dispatch.Refused)
    case FrFlowError.UnknownNode(id) => term.err(s"unknown node $id").as(Dispatch.Usage)
    case FrFlowError.LeanMissing => term.err(FrFlowError.LeanMissing.message).as(ExitCode(3))
    case other => term.err(s"error: ${Option(other.getMessage).getOrElse(other.toString)}").as(Dispatch.Refused)
