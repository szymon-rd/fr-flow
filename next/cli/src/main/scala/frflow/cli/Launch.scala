package frflow.cli

import cats.effect.std.Console
import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Help}
import frflow.api.view.Stop
import frflow.api.{FrFlowApi, FrFlowProject, Host}
import frflow.cli.command.{CliExtension, Command, Commands, Dispatch}
import frflow.cli.say.{Faults, Stops}
import frflow.cli.term.{Exit, Style, Terminal}
import frflow.cli.text.ReportText

/** A command run on a project, in the environment it runs in, with the layers on top it uses: `deciders` before the
  * project is opened (listing the first decider needs only its directory and the key), every other one on the project
  * opened over the live API in its directory (or what keeps its model from elaborating said).
  */
final class Launch(p: FrFlowProject, env: Map[String, String], layers: List[CliExtension]):
  def run(c: Command, term: Terminal, st: Style): IO[ExitCode] =
    val dir = p.directory(env)
    c match
      case Command.Deciders(as) => FrFlowApi.firstDecider[IO](dir, as, env).flatMap(l =>
          term.out(ReportText.listed(l))).as(Exit.Fine)
      case _                    => p.project.flatMap(_.fold(
          es => es.traverse_(e => term.err(s"error: ${Faults.text(e)}")).as(Exit.Refused),
          project => FrFlowApi.make[IO](project, dir, env).use(api => Dispatch(Host(api, dir, env), term, st,
            layers)(c))))

/** A project's command line run once: the arguments parsed (the help on a usage error), the command run, and what
  * stops it said with its exit code.
  */
object Launch:
  def apply(p: FrFlowProject, args: List[String]): IO[ExitCode] = IO(sys.env).flatMap { env =>
    val layers = p.extensions.collect { case c: CliExtension => c }
    val name = Option(p.directory(env).getFileName).map(_.toString).filter(_.nonEmpty).getOrElse("frflow")
    Sub(name, Commands.header(layers))(Commands.all(layers)).parse(args, env) match
      case Left(help)              => usage(help)
      case Right((command, plain)) => Terminal.live.flatMap(term =>
          new Launch(p, env, layers).run(command, term, Style.of(plain, env, term.interactive))
            .handleErrorWith(failed(term, _)))
  }

  /** The commands are listed once, under Subcommands: not again as a usage line each. */
  private def usage(help: Help): IO[ExitCode] =
    val once = if help.usage.size > 3 then help.copy(usage = List("[--plain] COMMAND [ARGS]...")) else help
    if help.errors.isEmpty then IO.println(once).as(Exit.Fine) else Console[IO].errorln(once).as(Exit.Usage)

  /** What stops a command, said; no Lean 3, an unknown node 2, anything else 1. */
  def failed(term: Terminal, e: Throwable): IO[ExitCode] = e match
    case s: Stop => Stops.lines(s).traverse_(term.err).as(s match
        case Stop.NoLean         => Exit.NoLean
        case Stop.UnknownNode(_) => Exit.Usage
        case _                   => Exit.Refused)
    case other   => term.err(s"error: ${Option(other.getMessage).getOrElse(other.toString)}").as(Exit.Refused)
