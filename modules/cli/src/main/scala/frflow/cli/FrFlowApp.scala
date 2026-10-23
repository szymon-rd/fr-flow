package frflow
package cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import cats.syntax.all.*
import com.monovore.decline.Command as Parser
import frflow.api.{FrFlowError, LiveApi}
import java.nio.file.Path

/** The command line of a knowledge base, which a project's main object extends:
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth")
  * }}}
  * `root` is the project's directory (`FRFLOW_ROOT` overrides it); `kernelPath`, FrFlow's Lean kernel
  * relative to the project's `lean/`. A usage error prints the help and exits 2.
  */
abstract class FrFlowApp(knowledge: => KnowledgeBase, root: String = ".", kernelPath: String = "../../../lean") extends IOApp:
  final def run(args: List[String]): IO[ExitCode] =
    IO(sys.env).flatMap(env => Parser(FrFlowApp.name(root), Commands.header)(Commands.all).parse(args, env) match
      case Right((command, looks)) => FrFlowApp.run(knowledge, root, kernelPath, command, looks, env)
      case Left(help) =>
        // The commands are listed once, under Subcommands: not again as a usage line each.
        val once = if help.usage.size > 3 then help.copy(usage = List("[--plain] COMMAND [ARGS]...")) else help
        if help.errors.isEmpty then IO.println(once).as(ExitCode.Success) else Console[IO].errorln(once).as(Dispatch.Usage))

object FrFlowApp:
  /** What the usage calls the command: the project's directory name. */
  def name(root: String): String =
    Option(Path.of(root).normalize.getFileName).map(_.toString).filter(n => n.nonEmpty && n != ".").getOrElse("frflow")

  def run(knowledge: => KnowledgeBase, root: String, kernelPath: String, command: Command, looks: Looks,
      env: Map[String, String]): IO[ExitCode] =
    for
      term <- Terminal.live
      st = style(looks, env, term.interactive)
      code <- LiveApi.fromEnv(knowledge, root, kernelPath, env).flatMap(api => Dispatch(api, term, st)(command)).handleErrorWith(failed(term, _))
    yield code

  /** Colors and Unicode on a terminal; plain ASCII with `--plain`, with `NO_COLOR`, or when the output is
    * not a terminal (CI, agents, files). Lines are cut to `COLUMNS` (bin/frflow sets it on a terminal); not cut otherwise.
    */
  def style(looks: Looks, env: Map[String, String], terminal: Boolean): Style =
    val color = !looks.plain && terminal && !env.contains("NO_COLOR")
    Style(color, unicode = color, env.get("COLUMNS").flatMap(_.toIntOption).filter(_ > 20))

  /** The one place failures become exit codes: the model's problems 1, an unknown node 2, no Lean 3. */
  private def failed(term: Terminal, e: Throwable): IO[ExitCode] = e match
    case FrFlowError.ModelProblems(ps) => ps.traverse_(p => term.err(s"error: $p")).as(Dispatch.Refused)
    case FrFlowError.UnknownNode(id) => term.err(s"unknown node $id").as(Dispatch.Usage)
    case FrFlowError.LeanMissing => term.err(FrFlowError.LeanMissing.message).as(ExitCode(3))
    case other => term.err(s"error: ${Option(other.getMessage).getOrElse(other.toString)}").as(Dispatch.Refused)
