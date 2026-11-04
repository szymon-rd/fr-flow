package frflow.cli.command

import cats.effect.{ExitCode, IO}
import cats.syntax.all.*
import com.monovore.decline.{Command as Sub, Opts}
import frflow.api.Host
import frflow.cli.command.Options.*
import frflow.cli.term.{Style, Terminal}
import frflow.cli.text.Depth
import frflow.core.name.NodeId
import frflow.decision.rules.Command as Decide

/** The command line: FrFlow's commands, then those of the layers on top (`CliExtension`). */
object Commands:
  def header(layers: List[CliExtension]): String = (List(
    """FrFlow: a small set of root statements refined by a DAG of small statements, each proven in Lean from its parts
      |(or its code tested against it) and decided by the developer.
      |
      |Read with tree, show, diff, inbox, find; decide with review, accept, reject, confirm, revisit, gone (rebase and
      |deciders for the ledger and who decides); prove with render, check, status, ci, export, scaffold. The web view
      |does the same in a browser: sbt "PROJECT/serve --as NAME".""".stripMargin) ++
    layers.map(_.header).filter(_.nonEmpty) :+ ("Exit codes: 0 fine; 1 something is not accepted or proven, or a " +
      "decision was refused; 2 a usage error or an unknown node; 3 no Lean (lake).")).mkString("\n\n")

  private def command(name: String, help: String)(opts: Opts[Command]): Sub[(Command, Boolean)] =
    Sub(name, help)((opts, plain).tupled)

  /** A layer's command: `run` on the project (with `--plain`, as FrFlow's take it). */
  def layer(name: String, help: String)(run: Opts[(Host[IO], Terminal, Style) => IO[ExitCode]])
      : Sub[(Command, Boolean)] = command(name, help)(run.map(Command.Layer(_)))

  private def decision(name: String, help: String)(make: Opts[(String => Decide, Option[NodeId])])
      : Sub[(Command, Boolean)] = command(name, help)((make, asked).mapN((m, a) => Command.Decision(m._1, m._2, a)))

  private val reading = List(
    command("tree", "the DAG from the roots (or from NODE): each node's mark, review state and statement")(
      node().orNone.map(Command.Tree(_))),
    command("show", "a node: what it says and why, what deciding it takes, where it sits, its proofs and code")(
      (node(), Opts.flag("full", "everything, nothing cut").orFalse.map(if _ then Depth.Full else Depth.Normal))
        .mapN(Command.Show(_, _))),
    command("diff", "what moved since NODE was decided: its fields, what it rests on, its parts, its code")(
      node().map(Command.Diff(_))),
    command("inbox", "what waits for the developer, in the order to decide it, and the decided nodes gone")(
      Opts(Command.Inbox)),
    command("find", "the nodes that govern a file, or whose words mention some words")(
      words("WORDS|PATH").map(Command.Find(_))))

  private val deciding = List(
    command("review", "decide what waits, node by node: [a]ccept [r]eject [s]kip [v]iew [q]uit (layers add keys)")(
      as.map(Command.Review(_))),
    decision("accept", "accept nodes (rejecting their rivals), checked and tested afresh first; --revisit names " +
      "decisions below the change to review again")((nodes, revisit).mapN((ns, r) =>
        ((why: String) => Decide.Accept(ns, why, r, Map.empty), ns.headOption.filter(_ => ns.size == 1)))),
    decision("reject", "reject a proposal, saying why: what the reason asks for is proposed instead, or it is removed")(
      node().map(n => ((why: String) => Decide.Reject(n, why, None), Some(n)))),
    decision("confirm", "accept the mechanical decisions in one batch (Lean proves them again; nothing in them is a " +
      "choice)")(Opts(((why: String) => Decide.Confirm(why), None))),
    decision("revisit", "ask that an accepted node be reviewed again: a change elsewhere may affect it")(
      node().map(n => ((why: String) => Decide.Revisit(n, why), Some(n)))),
    decision("gone", "agree that a decided node is gone from the model")(
      node().map(n => ((why: String) => Decide.Gone(n, why), Some(n)))),
    command("rebase", "accept the ledger as it reads now as where its committed history starts (after a merge, or " +
      "a committed change you accept); a listed decider only")((as, yes).mapN(Command.Rebase(_, _))),
    command("deciders", "list your key as the project's first decider (.frflow/deciders, signed by it): commit it")(
      Opts.option[String]("as", "the name you decide under").map(Command.Deciders(_))))

  private val proving = List(
    command("render", "write the Lean of the FrModel")(Opts(Command.Render)),
    command("check", "prove each node from its parts in Lean, test its code; record the results")(
      (node().orNone, json).mapN(Command.Check(_, _))),
    command("status", "the tree, the warnings and the summary; exits 1 unless the FrModel is complete")(
      json.map(Command.Status(_))),
    command("ci", "for CI: check everything, then status; exits 1 unless everything is proven and decided")(
      Opts(Command.Ci)),
    command("export", "write the snapshot (.frflow/kb.json) and print it")(Opts(Command.Export)),
    command("scaffold", "a proof file with a stub for each obligation the last check left open")(
      node().map(Command.Scaffold(_))))

  /** The command, and whether `--plain` was given before or after it. */
  def all(layers: List[CliExtension]): Opts[(Command, Boolean)] =
    val subs = reading ++ deciding ++ proving ++ layers.flatMap(_.commands)
    (plain, Opts.subcommands(subs.head, subs.tail*)).mapN { case (before, (c, after)) => (c, before || after) }
