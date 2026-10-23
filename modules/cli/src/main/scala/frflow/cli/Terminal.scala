package frflow.cli

import cats.effect.{IO, Ref}
import cats.effect.std.Console
import cats.syntax.all.*

/** Where the CLI writes and, on a terminal, reads: one small service, so the interactive review is
  * tested with scripted input.
  */
trait Terminal:
  /** Whether a person is there: input and output are a terminal. */
  def interactive: Boolean
  def out(lines: List[String]): IO[Unit]
  def err(line: String): IO[Unit]
  /** A line typed after `prompt`; none at the end of the input. */
  def read(prompt: String): IO[Option[String]]
  def out(line: String): IO[Unit] = out(List(line))

object Terminal:
  /** The process's own: interactive when the JVM has a console (stdin and stdout both a terminal). */
  def live: IO[Terminal] = IO(System.console() != null).map { tty =>
    new Terminal:
      val interactive: Boolean = tty
      def out(lines: List[String]): IO[Unit] = if lines.isEmpty then IO.unit else Console[IO].println(lines.mkString("\n"))
      def err(line: String): IO[Unit] = Console[IO].errorln(line)
      def read(prompt: String): IO[Option[String]] =
        Console[IO].print(prompt) *> IO.blocking(Option(scala.io.StdIn.readLine()))
  }

  /** A terminal typing `input`, line by line, and keeping what is written (prompts included). */
  final class Scripted(input: Ref[IO, List[String]], written: Ref[IO, Vector[String]], val interactive: Boolean) extends Terminal:
    def out(lines: List[String]): IO[Unit] = written.update(_ ++ lines)
    def err(line: String): IO[Unit] = written.update(_ :+ s"error: $line")
    def read(prompt: String): IO[Option[String]] =
      input.modify {
        case l :: rest => (rest, Some(l))
        case Nil => (Nil, None)
      }.flatTap(l => written.update(_ :+ (prompt + l.getOrElse(""))))
    def output: IO[Vector[String]] = written.get

  def scripted(input: List[String], interactive: Boolean = true): IO[Scripted] =
    (Ref.of[IO, List[String]](input), Ref.of[IO, Vector[String]](Vector.empty)).mapN(Scripted(_, _, interactive))
