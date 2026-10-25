package frflow.cli

import cats.effect.{ExitCode, IO}
import com.monovore.decline.Command as Sub
import frflow.api.{Extension, Host, View}

/** What a layer on top (an AI agent's tools, say) adds to the command line: its commands, listed after FrFlow's (build
  * them with `Commands.layer`), a line for the help, and what it shows in FrFlow's views of the project.
  */
trait CliExtension extends Extension:
  def commands: List[Sub[(Command, Boolean)]]
  def header: String = ""
  /** What it adds to a view, read once per command. */
  def contribute(host: Host, v: View): IO[Contribution] = IO.pure(Contribution.empty)

object CliExtension:
  /** One of a layer's commands, parsed: what it does on the project. */
  type CliRun = (Host, Terminal, Style) => IO[ExitCode]
