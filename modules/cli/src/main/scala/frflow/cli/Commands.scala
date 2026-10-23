package frflow.cli

import cats.syntax.all.*
import com.monovore.decline.Opts
import frflow.protocol.{NodeId, RequestId}

/** How output looks, as asked: `plain` forces ASCII without color; else a terminal decides (see `FrFlowApp.style`). */
final case class Looks(plain: Boolean)

/** A decision as asked: why (asked for on a terminal), by whom, and whether it is confirmed already. */
final case class Asked(reason: Option[String], as: Option[String], yes: Boolean)

/** A command line, parsed. */
enum Command:
  case Tree(from: Option[NodeId], full: Boolean, json: Boolean)
  case Show(node: NodeId, lean: Boolean, json: Boolean)
  case Diff(node: NodeId, json: Boolean)
  case Inbox(json: Boolean)
  case Review(as: Option[String])
  case Accept(nodes: List[NodeId], revisit: List[NodeId], asked: Asked)
  case Reject(node: NodeId, asked: Asked)
  case Confirm(asked: Asked)
  case Revisit(node: NodeId, asked: Asked)
  case Gone(node: NodeId, asked: Asked)
  case Ask(node: Option[NodeId], text: String, as: Option[String])
  case Close(requests: List[RequestId])
  case Render
  case Check(node: Option[NodeId], json: Boolean)
  case Status(json: Boolean)
  case Ci(json: Boolean)
  case Context(node: NodeId)
  case Find(query: String, json: Boolean)
  case Scaffold(node: NodeId)
  case Answer(to: String, text: String)

/** The command line: the developer's commands, then the agent's (their names are SKILL.md's). */
object Commands:
  val header: String =
    """FrFlow: one root refined by a DAG of small statements, each proven in Lean from its parts and decided by the developer.
      |
      |The developer reads with tree, show, diff, inbox; decides with review, accept, reject, confirm, revisit, gone;
      |asks with ask and close. The agent works with render, check, status, ci, context, find, scaffold, answer, inbox.
      |Exit codes: 0 fine; 1 something is not accepted or proven, or a decision was refused; 2 a usage error.""".stripMargin

  private val looks: Opts[Looks] =
    Opts.flag("plain", "ASCII without colors (also when NO_COLOR is set or the output is not a terminal)").orFalse.map(Looks.apply)

  private val json = Opts.flag("json", "print the API's typed value as JSON").orFalse
  private def node(name: String = "NODE") = Opts.argument[String](name).map(NodeId(_))
  private val as = Opts.option[String]("as", "who decides (default: FRFLOW_AS, or the name your key is filed under)").orNone
  private val yes = Opts.flag("yes", "decide without asking (needed without a terminal)", "y").orFalse
  private val reason = Opts.option[String]("reason", "why: kept as part of the theory (asked for on a terminal)", "m").orNone
  private val asked = (reason, as, yes).mapN(Asked.apply)
  private def words(name: String) = Opts.arguments[String](name).map(_.toList.mkString(" "))

  private def command(name: String, help: String)(opts: Opts[Command]): Opts[(Command, Looks)] =
    Opts.subcommand(name, help)((opts, looks).tupled)

  private val developer = List(
    command("tree", "the DAG from the root (or from NODE): each node's status, review state and statement")(
      (node().orNone, Opts.flag("all", "every statement in full, wrapped (not cut to the width)").orFalse, json).mapN(Command.Tree.apply)),
    command("show", "a node: what it says and why, what changed, its parts and parents, proofs, examples, code, decisions")(
      (node(), Opts.flag("lean", "with the generated Lean, the obligations and the proof file").orFalse, json).mapN(Command.Show.apply)),
    command("diff", "what changed since NODE was decided: its fields, what moved above it, its code")((node(), json).mapN(Command.Diff.apply)),
    command("inbox", "what waits for whom: requests, answers, decisions to take, the agent's tasks; then the tree")(json.map(Command.Inbox.apply)),
    command("review", "decide what waits, node by node, parents first: [a]ccept [r]eject [s]kip [q]uit [?]ask")(as.map(Command.Review.apply)),
    command("accept", "accept nodes (rejecting their rivals); --revisit names decisions below a change to review again")(
      (Opts.arguments[String]("NODE").map(_.toList.map(NodeId(_))),
        Opts.options[String]("revisit", "a decision below the change that it may affect").orEmpty.map(_.map(NodeId(_))), asked)
        .mapN(Command.Accept.apply)),
    command("reject", "reject a proposal, saying why: the agent proposes what the reason asks for, or removes it")(
      (node(), asked).mapN(Command.Reject.apply)),
    command("confirm", "accept the mechanical decisions in one batch (Lean proves them again; nothing in them is a choice)")(
      asked.map(Command.Confirm.apply)),
    command("revisit", "ask that an accepted node be reviewed again: a change elsewhere may affect it")((node(), asked).mapN(Command.Revisit.apply)),
    command("gone", "agree that a decided node is gone from the model")((node(), asked).mapN(Command.Gone.apply)),
    command("ask", "ask the agent for a change on NODE (or, with --idea, about the whole idea)")(
      (Opts.flag("idea", "about the whole idea, not one node").map(_ => Option.empty[NodeId]).orElse(node().map(Some(_))), words("TEXT"), as)
        .mapN(Command.Ask.apply)),
    command("close", "close requests: an answer read, or a request withdrawn")(
      Opts.arguments[String]("REQUEST").map(rs => Command.Close(rs.toList.map(RequestId(_))))))

  private val agent = List(
    command("render", "generate Lean and the snapshot .frflow/kb.json from the Scala definitions")(Opts(Command.Render)),
    command("check", "render, prove each node from its parts, record the results")((node().orNone, json).mapN(Command.Check.apply)),
    command("status", "the tree, the proofs, what is trusted; exits 1 unless the knowledge base is complete")(json.map(Command.Status.apply)),
    command("ci", "for CI: check, then status; exits 1 unless everything is proven and decided")(json.map(Command.Ci.apply)),
    command("context", "everything needed to work on NODE (for agents and people)")(node().map(Command.Context.apply)),
    command("find", "the nodes that govern a file, or what mentions some words")((words("WORDS|PATH"), json).mapN(Command.Find.apply)),
    command("scaffold", "a proof file for the obligations automation did not prove")(node().map(Command.Scaffold.apply)),
    command("answer", "reply to the developer's request; with a NODE instead, tell them about work they did not ask for")(
      (Opts.argument[String]("REQUEST|NODE"), words("TEXT")).mapN(Command.Answer.apply)))

  val all: Opts[(Command, Looks)] = (developer ++ agent).reduce(_ orElse _)
