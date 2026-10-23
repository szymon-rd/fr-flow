package frflow
package cli

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.api.{Decide, FrFlowError, LiveApi}
import frflow.protocol.{NodeId, RequestId}
import java.nio.file.Path

/** The command line of a knowledge base, which a project's main object extends:
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth")
  * }}}
  * `root` is the project's directory (`FRFLOW_ROOT` overrides it); `kernelPath`, FrFlow's Lean kernel
  * relative to the project's `lean/`. A usage error prints the help and exits 2.
  */
abstract class FrFlowApp(knowledge: => KnowledgeBase, root: String = ".", kernelPath: String = "../../../lean") extends IOApp:
  final def run(args: List[String]): IO[ExitCode] = IO(sys.env).flatMap { env =>
    val name = Option(Path.of(root).normalize.getFileName).map(_.toString).filter(n => n.nonEmpty && n != ".").getOrElse("frflow")
    Sub(name, Commands.header)(Commands.all).parse(args, env) match
      case Right((command, plain)) =>
        for
          term <- Terminal.live
          st = Style.of(plain, env, term.interactive)
          code <- LiveApi.fromEnv(knowledge, root, kernelPath, env).flatMap(api => Dispatch(api, term, st)(command))
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
  def live: IO[Terminal] = IO(System.console() != null).map { tty =>
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
  case Ask(node: Option[NodeId], text: String, as: Option[String])
  case Close(requests: List[RequestId])
  case Render
  case Check(node: Option[NodeId], json: Boolean)
  case Status(json: Boolean)
  case Ci
  case Find(query: String)
  case Scaffold(node: NodeId)
  case Answer(to: String, text: String)

/** The command line: the developer's commands, then the agent's (their names are SKILL.md's). */
object Commands:
  val header: String =
    """FrFlow: one root refined by a DAG of small statements, each proven in Lean from its parts and decided by the developer.
      |
      |The developer reads with tree, show, diff, inbox; decides with review, accept, reject, confirm, revisit, gone;
      |asks with ask and close. The agent works with render, check, status, ci, context, find, scaffold, answer, inbox.
      |Exit codes: 0 fine; 1 something is not accepted or proven, or a decision was refused; 2 a usage error; 3 no Lean.""".stripMargin

  private val plain = Opts.flag("plain", "ASCII without colors (also when NO_COLOR is set or the output is not a terminal)").orFalse
  private val json = Opts.flag("json", "print the typed value as JSON, each node in brief").orFalse
  private def node(name: String = "NODE") = Opts.argument[String](name).map(NodeId(_))
  private val as = Opts.option[String]("as", "who decides (default: FRFLOW_AS, or the name your key is filed under)").orNone
  private val yes = Opts.flag("yes", "decide without asking (needed without a terminal)", "y").orFalse
  private val reason = Opts.option[String]("reason", "why: kept as part of the theory (asked for on a terminal)", "m").orNone
  private val asked = (reason, as, yes).mapN(Asked.apply)
  private def words(name: String) = Opts.arguments[String](name).map(_.toList.mkString(" "))

  private def command(name: String, help: String)(opts: Opts[Command]): Sub[(Command, Boolean)] = Sub(name, help)((opts, plain).tupled)
  private def decision(name: String, help: String)(make: Opts[String => Decide]): Sub[(Command, Boolean)] =
    command(name, help)((make, asked).mapN(Command.Decision.apply))

  private val developer = List(
    command("tree", "the DAG from the root (or from NODE): each node's status, review state and statement")(
      (node().orNone, json).mapN(Command.Tree.apply)),
    command("show", "a node: what it says and why, what changed, its parts and parents, proofs, examples, code, decisions")(
      (node(), Opts.flag("full", "everything, nothing cut: what context prints").orFalse.map(if _ then Depth.Full else Depth.Normal), json)
        .mapN(Command.Show.apply)),
    command("diff", "what changed since NODE was decided: its fields, what moved above it, its code")(node().map(Command.Diff.apply)),
    command("inbox", "what waits for whom: requests, answers, decisions to take, the agent's tasks")(json.map(Command.Inbox.apply)),
    command("review", "decide what waits, node by node, parents first: [a]ccept [r]eject [s]kip [v]iew [q]uit [?]ask")(as.map(Command.Review.apply)),
    decision("accept", "accept nodes (rejecting their rivals); --revisit names decisions below a change to review again")(
      (Opts.arguments[String]("NODE").map(_.toList.map(NodeId(_))),
        Opts.options[String]("revisit", "a decision below the change that it may affect").orEmpty.map(_.map(NodeId(_))))
        .mapN((nodes, revisit) => Decide.Accept(nodes, _, revisit))),
    decision("reject", "reject a proposal, saying why: the agent proposes what the reason asks for, or removes it")(node().map(n => Decide.Reject(n, _))),
    decision("confirm", "accept the mechanical decisions in one batch (Lean proves them again; nothing in them is a choice)")(Opts(Decide.Confirm(_))),
    decision("revisit", "ask that an accepted node be reviewed again: a change elsewhere may affect it")(node().map(n => Decide.Revisit(n, _))),
    decision("gone", "agree that a decided node is gone from the model")(node().map(n => Decide.Gone(n, _))),
    command("ask", "ask the agent for a change on NODE (or, with --idea, about the whole idea)")(
      (Opts.flag("idea", "about the whole idea, not one node").map(_ => Option.empty[NodeId]).orElse(node().map(Some(_))), words("TEXT"), as)
        .mapN(Command.Ask.apply)),
    command("close", "close requests: an answer read, or a request withdrawn")(
      Opts.arguments[String]("REQUEST").map(rs => Command.Close(rs.toList.map(RequestId(_))))))

  private val agent = List(
    command("render", "generate Lean and the snapshot .frflow/kb.json from the Scala definitions")(Opts(Command.Render)),
    command("check", "render, prove each node from its parts, record the results")((node().orNone, json).mapN(Command.Check.apply)),
    command("status", "the tree and the summary; exits 1 unless the knowledge base is complete")(json.map(Command.Status.apply)),
    command("ci", "for CI: check, then status; exits 1 unless everything is proven and decided")(Opts(Command.Ci)),
    command("context", "show --full: everything needed to work on NODE, with the idea and what it rests on")(node().map(Command.Show(_, Depth.Full, json = false))),
    command("find", "the nodes that govern a file, or what mentions some words")(words("WORDS|PATH").map(Command.Find.apply)),
    command("scaffold", "a proof file with a stub for each obligation the last check left open")(node().map(Command.Scaffold.apply)),
    command("answer", "reply to the developer's request; with a NODE instead, tell them about work they did not ask for")(
      (Opts.argument[String]("REQUEST|NODE"), words("TEXT")).mapN(Command.Answer.apply)))

  /** The command, and whether `--plain` was given before or after it. */
  val all: Opts[(Command, Boolean)] =
    val subs = developer ++ agent
    (plain, Opts.subcommands(subs.head, subs.tail*)).mapN { case (before, (c, after)) => (c, before || after) }
