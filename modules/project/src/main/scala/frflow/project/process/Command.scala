package frflow.project.process

import cats.effect.{Async, Ref}
import cats.effect.syntax.all.*
import cats.syntax.all.*
import fs2.io.process.{ProcessBuilder, Processes}
import fs2.text
import java.nio.file.Path
import scala.concurrent.duration.FiniteDuration

/** A program the live interpreters run (`lake`, `git`), how long one run of it may take, and what of its output a
  * run keeps.
  */
final case class Command(program: String, timeout: FiniteDuration, output: Output)

object Command:
  /** One run in `dir`, with `env` added to the environment, stopped after the timeout or on cancel; its output kept
    * either way.
    */
  def run[F[_]: Async: Processes](c: Command, args: List[String], dir: Path, env: Map[String, String]): F[Exited] =
    val merged = c.output == Output.Merged
    Ref.of[F, Vector[String]](Vector.empty).flatMap { out =>
      val exec = ProcessBuilder(c.program, args).withWorkingDirectory(fs2.io.file.Path.fromNioPath(dir))
        .withExtraEnv(env).spawn[F].use { p =>
          val lines = (s: fs2.Stream[F, Byte]) => s.through(text.utf8.decode).through(text.lines)
          val read = if merged then lines(p.stdout).merge(lines(p.stderr)).evalMap(l => out.update(_ :+ l))
            else p.stdout.through(text.utf8.decode).evalMap(chunk => out.update(_ :+ chunk))
              .concurrently(p.stderr.drain)
          read.compile.drain *> p.exitValue
        }
      val joined = (o: Vector[String]) => if merged then o.mkString("\n") else o.mkString
      exec.flatMap(code => out.get.map(o => Exited.Code(code, joined(o))))
        .timeoutTo(c.timeout, out.get.map(o => Exited.TimedOut(joined(o) + s"\ntimed out after ${c.timeout}")))
    }
