package frflow.cli

import cats.effect.{IO, Ref}
import cats.syntax.all.*

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

object Scripted:
  def apply(input: List[String], interactive: Boolean = true): IO[Scripted] =
    (Ref.of[IO, List[String]](input), Ref.of[IO, Vector[String]](Vector.empty)).mapN(new Scripted(_, _, interactive))
