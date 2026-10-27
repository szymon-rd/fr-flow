package frflow.cli
package command

import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.api.Decide
import frflow.protocol.NodeId

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
  val json: Opts[Boolean] = Opts.flag("json", "print the output as JSON, each node in brief").orFalse
  /** A node, by its id or its val's name (`grantWhenFree` is `GrantWhenFree`). */
  def node(name: String = "NODE"): Opts[NodeId] = Opts.argument[String](name).map(n => NodeId(n.capitalize))
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
      (Opts.arguments[String]("NODE").map(_.toList.map(n => NodeId(n.capitalize))),
        Opts.options[String]("revisit", "a decision below the change that it may affect").orEmpty
          .map(_.map(n => NodeId(n.capitalize))))
        .mapN((nodes, revisit) => Decide.Accept(nodes, _, revisit))),
    decision("reject", "reject a proposal, saying why: what the reason asks for is proposed instead, or it is removed")(node().map(n => Decide.Reject(n, _))),
    decision("confirm", "accept the mechanical decisions in one batch (Lean proves them again; nothing in them is a choice)")(Opts(Decide.Confirm(_))),
    decision("revisit", "ask that an accepted node be reviewed again: a change elsewhere may affect it")(node().map(n => Decide.Revisit(n, _))),
    decision("gone", "agree that a decided node is gone from the model")(node().map(n => Decide.Gone(n, _))))

  private val proving = List(
    command("render", "generate Lean and the snapshot .frflow/kb.json from the Scala definitions")(Opts(Command.Render)),
    command("check", "render, prove each node from its parts, record the results")((node().orNone, json).mapN(Command.Check.apply)),
    command("status", "the tree and the summary; exits 1 unless the FrModel is complete")(json.map(Command.Status.apply)),
    command("ci", "for CI: check, then status; exits 1 unless everything is proven and decided")(Opts(Command.Ci)),
    command("find", "the nodes that govern a file, or what mentions some words")(words("WORDS|PATH").map(Command.Find.apply)),
    command("scaffold", "a proof file with a stub for each obligation the last check left open")(node().map(Command.Scaffold.apply)))

  /** The command, and whether `--plain` was given before or after it. */
  def all(layers: List[CliExtension] = Nil): Opts[(Command, Boolean)] =
    val subs = developer ++ proving ++ layers.flatMap(_.commands)
    (plain, Opts.subcommands(subs.head, subs.tail*)).mapN { case (before, (c, after)) => (c, before || after) }
