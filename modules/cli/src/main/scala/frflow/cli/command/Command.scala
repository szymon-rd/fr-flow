package frflow.cli.command

import cats.effect.{ExitCode, IO}
import frflow.api.Host
import frflow.cli.term.{Style, Terminal}
import frflow.cli.text.Depth
import frflow.core.name.NodeId
import frflow.decision.rules.Command as Decide

/** A command as parsed: what it reads, decides or proves. */
enum Command:
  case Tree(from: Option[NodeId])
  case Show(node: NodeId, depth: Depth)
  case Diff(node: NodeId)
  case Inbox
  case Find(query: String)
  case Review(as: Option[String])
  /** What it records, given the reason; the node it is about, when one (a gone node is said so). */
  case Decision(make: String => Decide, about: Option[NodeId], asked: Asked)
  /** The ledger as it reads now accepted as the start of its committed history. */
  case Rebase(as: Option[String], yes: Boolean)
  /** The developer's key listed as the project's first decider. */
  case Deciders(as: String)
  case Render
  case Check(node: Option[NodeId], json: Boolean)
  case Status(json: Boolean)
  case Ci
  case Export
  case Scaffold(node: NodeId)
  /** One of a layer's commands (`CliExtension`): what it does on the project. */
  case Layer(run: (Host[IO], Terminal, Style) => IO[ExitCode])
