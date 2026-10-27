package frflow.cli.command

import cats.effect.IO
import com.monovore.decline.Command as Sub
import frflow.api.view.View
import frflow.api.{Extension, Host}
import frflow.cli.review.ReviewKey
import frflow.cli.term.Style
import frflow.cli.text.Contribution

/** What a layer on top (an AI agent's tools, say) adds to the command line: its commands, listed after FrFlow's (build
  * them with `Commands.layer`), a paragraph for the help, what it shows in FrFlow's views of the project (read once
  * per command), and keys it offers on a node in the review. A layer proposes and asks; it never decides.
  */
trait CliExtension extends Extension:
  def commands: List[Sub[(Command, Boolean)]]
  def header: String = ""
  def contribute(host: Host[IO], v: View, st: Style): IO[Contribution]
  def keys(host: Host[IO]): List[ReviewKey]
