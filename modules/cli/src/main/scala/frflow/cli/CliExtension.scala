package frflow.cli

import cats.effect.{ExitCode, IO}
import com.monovore.decline.Command as Sub
import frflow.api.{Developer, Extension, Host, View}
import frflow.protocol.{NodeId, Reviewed}

/** What a layer on top (an AI agent's tools, say) adds to the command line: its commands, listed after FrFlow's (build
  * them with `Commands.layer`), a line for the help, and what it shows in FrFlow's views of the project.
  */
trait CliExtension extends Extension:
  def commands: List[Sub[(Command, Boolean)]]
  def header: String = ""
  /** What it adds to a view, read once per command. */
  def contribute(host: Host, v: View): IO[Contribution] = IO.pure(Contribution.empty)

/** One of a layer's commands, parsed: what it does on the project. */
type CliRun = (Host, Terminal, Style) => IO[ExitCode]

/** A key the review offers on a node: `act` runs on it, and the review moves on to the next. */
final case class ReviewKey(key: String, label: String, act: (Developer, Reviewed, Terminal, Style) => IO[Unit])

/** What layers add to a view: the nodes they hold back from the developer's queue (`aside`), a word shown beside a node
  * (`marks`), warnings `status` and `ci` fail on, phrases for the summary's "Waiting:" line, sections closing the inbox,
  * lines closing a node's `show`, and keys for the review.
  */
final case class Contribution(aside: Set[NodeId] = Set.empty, marks: Map[NodeId, String] = Map.empty,
    warnings: List[String] = Nil, waiting: Style => List[String] = _ => Nil, inbox: Style => List[String] = _ => Nil,
    node: (NodeId, Style) => List[String] = (_, _) => Nil, review: List[ReviewKey] = Nil):
  def ++(o: Contribution): Contribution =
    Contribution(aside ++ o.aside, marks ++ o.marks, warnings ++ o.warnings, st => waiting(st) ++ o.waiting(st),
      st => inbox(st) ++ o.inbox(st), (id, st) => node(id, st) ++ o.node(id, st), review ++ o.review)

object Contribution:
  val empty: Contribution = Contribution()
  def all(cs: List[Contribution]): Contribution = cs.foldLeft(empty)(_ ++ _)
