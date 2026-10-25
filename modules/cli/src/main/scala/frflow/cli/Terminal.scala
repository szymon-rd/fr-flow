package frflow.cli

import cats.effect.IO
import cats.effect.std.Console

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
