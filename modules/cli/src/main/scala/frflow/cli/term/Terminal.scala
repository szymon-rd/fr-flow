package frflow.cli.term

import cats.effect.IO
import cats.effect.std.Console
import cats.syntax.all.*

/** Where the CLI writes and, on a terminal, reads: the developer's answers in the review and before a decision. Tests
  * pass one with scripted input (`Scripted`).
  */
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
  def attached[C](console: Option[C], isTerminal: C => Option[Boolean]): Boolean =
    console.exists(isTerminal(_).getOrElse(true))

  private def isTerminal(c: java.io.Console): Option[Boolean] =
    Either.catchNonFatal(classOf[java.io.Console].getMethod("isTerminal")).toOption
      .map(_.invoke(c) == java.lang.Boolean.TRUE)

  private val Token = "(?s)\u001b\\[[0-9;]*m|.".r

  /** What the terminal is given to show: control characters dropped (an escape sequence in what an agent wrote
    * could move the cursor and repaint what the developer reads before a prompt), but new lines, tabs and the colors
    * `Style` adds.
    */
  def clean(s: String): String = Token.findAllIn(s).filter(t =>
    t.length > 1 || t == "\n" || t == "\t" || t.forall(!Character.isISOControl(_))).mkString

  def live: IO[Terminal] = IO(attached(Option(System.console()), isTerminal)).map { tty =>
    new Terminal:
      val interactive: Boolean = tty
      def out(lines: List[String]): IO[Unit] =
        if lines.isEmpty then IO.unit else Console[IO].println(clean(lines.mkString("\n")))
      def err(line: String): IO[Unit] = Console[IO].errorln(clean(line))
      def read(prompt: String): IO[Option[String]] =
        Console[IO].print(clean(prompt)) *> IO.blocking(Option(scala.io.StdIn.readLine()))
  }
