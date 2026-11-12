package frflow.project.process

import cats.effect.{Async, Ref}
import cats.effect.syntax.all.*
import cats.syntax.all.*
import fs2.io.process.{Process, ProcessBuilder, Processes}
import fs2.text
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration

/** A program the live interpreters run (`rocq`, `git`), how long one run of it may take, and what of its output a
  * run keeps.
  */
final case class Command(program: String, timeout: FiniteDuration, output: Output)

object Command:
  /** What a run wrote, as it goes: to its standard output (or, merged, to either, by line), and to its standard
    * error.
    */
  private final case class Kept[F[_]](out: Ref[F, Vector[String]], err: Ref[F, Vector[String]])

  /** One run in `dir`, with `env` added to the environment, stopped after the timeout or on cancel; its output kept
    * either way.
    */
  def run[F[_]: Async: Processes](c: Command, args: List[String], dir: Path, env: Map[String, String]): F[Exited] =
    val empty = Ref.of[F, Vector[String]](Vector.empty)
    (empty, empty).mapN(Kept(_, _)).flatMap { kept =>
      val exec = ProcessBuilder(c.program, args).withWorkingDirectory(fs2.io.file.Path.fromNioPath(dir))
        .withExtraEnv(env).spawn[F].use(p => read(c.output, p, kept) *> p.exitValue)
      exec.flatMap(code => said(c.output, kept, code == 0).map(Exited.Code(code, _)))
        .timeoutTo(c.timeout,
          said(c.output, kept, true).map(o => Exited.TimedOut(o + s"\ntimed out after ${c.timeout}")))
    }

  private def read[F[_]: Async](mode: Output, p: Process[F], kept: Kept[F]): F[Unit] =
    val lines = (s: fs2.Stream[F, Byte]) => s.through(text.utf8.decode).through(text.lines)
    val chunks = (s: fs2.Stream[F, Byte], to: Ref[F, Vector[String]]) =>
      s.through(text.utf8.decode).evalMap(chunk => to.update(_ :+ chunk))
    (mode match
      case Output.Merged   => lines(p.stdout).merge(lines(p.stderr)).evalMap(l => kept.out.update(_ :+ l))
      case Output.Standard => chunks(p.stdout, kept.out).concurrently(p.stderr.drain)
      case Output.ByExit   => chunks(p.stdout, kept.out).concurrently(chunks(p.stderr, kept.err))
    ).compile.drain

  private def said[F[_]: Async](mode: Output, kept: Kept[F], ok: Boolean): F[String] = mode match
    case Output.Merged          => kept.out.get.map(_.mkString("\n"))
    case Output.ByExit if !ok   => kept.err.get.map(_.mkString)
    case _                      => kept.out.get.map(_.mkString)
