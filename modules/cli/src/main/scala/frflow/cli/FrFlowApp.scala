package frflow
package cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import cats.syntax.all.*
import com.monovore.decline.Command as Parser
import frflow.api.{FrFlowError, LiveApi}
import frflow.check.Workspace
import frflow.ledger.KeyStore
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
      case Right((command, looks)) => FrFlowApp.run(knowledge, root, kernelPath, command, looks)
      case Left(help) if help.errors.isEmpty => IO.println(help).as(ExitCode.Success)
      case Left(help) => Console[IO].errorln(help).as(Run.Usage))

object FrFlowApp:
  /** What the usage calls the command: the project's directory name. */
  def name(root: String): String =
    Option(Path.of(root).normalize.getFileName).map(_.toString).filter(n => n.nonEmpty && n != ".").getOrElse("frflow")

  def run(knowledge: => KnowledgeBase, root: String, kernelPath: String, command: Command, looks: Looks): IO[ExitCode] =
    for
      env <- IO(sys.env)
      home <- IO(sys.props.getOrElse("user.home", "."))
      term <- Terminal.live
      st <- style(looks, env, term.interactive)
      ws = Workspace(Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize, kernelPath)
      code <- IO.blocking(knowledge).flatMap(kb => LiveApi(kb, ws, KeyStore.keyFile(env, Path.of(home)), env))
        .flatMap(api => Run(api, term, st)(command))
        .handleErrorWith(failed(term, _))
    yield code

  /** Colors and Unicode on a terminal; plain ASCII with `--plain`, with `NO_COLOR`, or when the output is
    * not a terminal (CI, agents, files); `--color` forces them. Lines are cut to `--width`, `COLUMNS`, or
    * the terminal's width; not cut otherwise.
    */
  def style(looks: Looks, env: Map[String, String], terminal: Boolean): IO[Style] =
    val color = !looks.plain && (looks.color || (terminal && !env.contains("NO_COLOR")))
    val width = looks.width.orElse(env.get("COLUMNS").flatMap(_.toIntOption)) match
      case Some(w) => IO.pure(Some(w))
      case None => if terminal then terminalWidth else IO.pure(None)
    width.map(w => Style(color, unicode = color, w.filter(_ > 20)))

  /** The terminal's columns, as `stty` reports them. */
  private def terminalWidth: IO[Option[Int]] = IO.blocking {
    val p = ProcessBuilder("sh", "-c", "stty size < /dev/tty").redirectErrorStream(true).start()
    val out = String(p.getInputStream.readAllBytes()).trim
    Option.when(p.waitFor() == 0)(out.split("\\s+").lastOption.flatMap(_.toIntOption)).flatten
  }.handleError(_ => None)

  /** The one place failures become exit codes: the model's problems 1, an unknown node 2, no Lean 3. */
  private def failed(term: Terminal, e: Throwable): IO[ExitCode] = e match
    case FrFlowError.ModelProblems(ps) => ps.traverse_(p => term.err(s"error: $p")).as(Run.Refused)
    case FrFlowError.UnknownNode(id) => term.err(s"unknown node $id").as(Run.Usage)
    case FrFlowError.LeanMissing => term.err(FrFlowError.LeanMissing.message).as(ExitCode(3))
    case other => term.err(s"error: ${Option(other.getMessage).getOrElse(other.toString)}").as(Run.Refused)
