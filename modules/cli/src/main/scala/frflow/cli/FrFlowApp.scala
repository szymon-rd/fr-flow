package frflow
package cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.api.{Decide, Extension, FrFlowError, FrFlowProject, Host, LiveApi}
import frflow.protocol.NodeId
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

/** Where the CLI writes and, on a terminal, reads: a service, so the review is tested with scripted input. */
trait Terminal:
  def interactive: Boolean
  def out(lines: List[String]): IO[Unit]
  def err(line: String): IO[Unit]
  /** None at the end of the input. */
  def read(prompt: String): IO[Option[String]]
  def out(line: String): IO[Unit] = out(List(line))

object Terminal:
  /** From JDK 22 `System.console()` is there even when the output is redirected: `Console.isTerminal` (JDK 22, so
    * read by reflection: FrFlow builds on 21) says whether it is a terminal.
    */
  private[cli] def attached[C](console: Option[C], isTerminal: C => Option[Boolean]): Boolean =
    console.exists(isTerminal(_).getOrElse(true))
  private def isTerminal(c: java.io.Console): Option[Boolean] =
    scala.util.Try(classOf[java.io.Console].getMethod("isTerminal")).toOption.map(_.invoke(c) == java.lang.Boolean.TRUE)

  def live: IO[Terminal] = IO(attached(Option(System.console()), isTerminal)).map { tty =>
    new Terminal:
      val interactive: Boolean = tty
      def out(lines: List[String]): IO[Unit] = if lines.isEmpty then IO.unit else Console[IO].println(lines.mkString("\n"))
      def err(line: String): IO[Unit] = Console[IO].errorln(line)
      def read(prompt: String): IO[Option[String]] = Console[IO].print(prompt) *> IO.blocking(Option(scala.io.StdIn.readLine()))
  }

/** A decision as asked: why (asked for on a terminal), by whom, and whether it is confirmed already. */
final case class Asked(reason: Option[String], as: Option[String], yes: Boolean)

enum Command:
  case Tree(from: Option[NodeId], json: Boolean)
  case Show(node: NodeId, depth: Depth, json: Boolean)
  case Diff(node: NodeId)
  case Inbox(json: Boolean)
  case Review(as: Option[String])
  /** What it records, given the reason. */
  case Decision(make: String => Decide, asked: Asked)
  case Render
  case Check(node: Option[NodeId], json: Boolean)
  case Status(json: Boolean)
  case Ci
  case Find(query: String)
  case Scaffold(node: NodeId)
  /** One of a layer's commands (see `CliExtension`). */
  case Layer(run: CliRun)

/** The command line: FrFlow's commands, then those of the layers on top (`CliExtension`). */
object Commands:
  def header(layers: List[CliExtension] = Nil): String =
    ("""FrFlow: one root refined by a DAG of small statements, each proven in Lean from its parts and decided by the developer.
      |
      |The developer writes IDEA.md (what the system is for) and accepts it; the root and its parts follow, as Scala, each
      |decided in turn. Read with tree, show, diff, inbox, find; decide with review, accept, reject, confirm, revisit, gone;
      |prove with render, check, status, ci, scaffold. The web view does the same in a browser: sbt "PROJECT/serve --as NAME".""".stripMargin ::
      layers.map(_.header).filter(_.nonEmpty) :::
      List("Exit codes: 0 fine; 1 something is not accepted or proven, or a decision was refused; 2 a usage error; 3 no Lean (lake).")
    ).mkString("\n")

  val plain: Opts[Boolean] = Opts.flag("plain", "ASCII without colors (also when NO_COLOR is set or the output is not a terminal)").orFalse
  val json: Opts[Boolean] = Opts.flag("json", "print the typed value as JSON, each node in brief").orFalse
  def node(name: String = "NODE"): Opts[NodeId] = Opts.argument[String](name).map(NodeId(_))
  val as: Opts[Option[String]] = Opts.option[String]("as", "who decides (default: FRFLOW_AS, or the name your key is filed under)").orNone
  private val yes = Opts.flag("yes", "decide without asking (needed without a terminal)", "y").orFalse
  private val reason = Opts.option[String]("reason", "why: kept as part of the theory (asked for on a terminal)", "m").orNone
  private val asked = (reason, as, yes).mapN(Asked.apply)
  def words(name: String): Opts[String] = Opts.arguments[String](name).map(_.toList.mkString(" "))

  private def command(name: String, help: String)(opts: Opts[Command]): Sub[(Command, Boolean)] = Sub(name, help)((opts, plain).tupled)
  /** A layer's command: `run` on the project (with `--plain`, as FrFlow's take it). */
  def layer(name: String, help: String)(run: Opts[CliRun]): Sub[(Command, Boolean)] = command(name, help)(run.map(Command.Layer(_)))
  private def decision(name: String, help: String)(make: Opts[String => Decide]): Sub[(Command, Boolean)] =
    command(name, help)((make, asked).mapN(Command.Decision.apply))

  private val developer = List(
    command("tree", "the DAG from the root (or from NODE): each node's status, review state and statement")(
      (node().orNone, json).mapN(Command.Tree.apply)),
    command("show", "a node: what it says and why, what changed, its parts and parents, proofs, examples, code, decisions")(
      (node(), Opts.flag("full", "everything, nothing cut").orFalse.map(if _ then Depth.Full else Depth.Normal), json)
        .mapN(Command.Show.apply)),
    command("diff", "what changed since NODE was decided: its fields, what moved above it, its code")(node().map(Command.Diff.apply)),
    command("inbox", "what waits for the developer: IDEA.md, the decisions to take, in order, and the decided nodes gone")(json.map(Command.Inbox.apply)),
    command("review", "decide what waits, node by node, parents first: [a]ccept [r]eject [s]kip [v]iew [q]uit (layers may add keys)")(as.map(Command.Review.apply)),
    decision("accept", "accept nodes (rejecting their rivals); --revisit names decisions below a change to review again")(
      (Opts.arguments[String]("NODE").map(_.toList.map(NodeId(_))),
        Opts.options[String]("revisit", "a decision below the change that it may affect").orEmpty.map(_.map(NodeId(_))))
        .mapN((nodes, revisit) => Decide.Accept(nodes, _, revisit))),
    decision("reject", "reject a proposal, saying why: what the reason asks for is proposed instead, or it is removed")(node().map(n => Decide.Reject(n, _))),
    decision("confirm", "accept the mechanical decisions in one batch (Lean proves them again; nothing in them is a choice)")(Opts(Decide.Confirm(_))),
    decision("revisit", "ask that an accepted node be reviewed again: a change elsewhere may affect it")(node().map(n => Decide.Revisit(n, _))),
    decision("gone", "agree that a decided node is gone from the model")(node().map(n => Decide.Gone(n, _))))

  private val proving = List(
    command("render", "generate Lean and the snapshot .frflow/kb.json from the Scala definitions")(Opts(Command.Render)),
    command("check", "render, prove each node from its parts, record the results")((node().orNone, json).mapN(Command.Check.apply)),
    command("status", "the tree and the summary; exits 1 unless the knowledge base is complete")(json.map(Command.Status.apply)),
    command("ci", "for CI: check, then status; exits 1 unless everything is proven and decided")(Opts(Command.Ci)),
    command("find", "the nodes that govern a file, or what mentions some words")(words("WORDS|PATH").map(Command.Find.apply)),
    command("scaffold", "a proof file with a stub for each obligation the last check left open")(node().map(Command.Scaffold.apply)))

  /** The command, and whether `--plain` was given before or after it. */
  def all(layers: List[CliExtension] = Nil): Opts[(Command, Boolean)] =
    val subs = developer ++ proving ++ layers.flatMap(_.commands)
    (plain, Opts.subcommands(subs.head, subs.tail*)).mapN { case (before, (c, after)) => (c, before || after) }
