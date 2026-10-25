package frflow
package check
package process

import cats.effect.{IO, Ref}
import fs2.io.process.ProcessBuilder
import fs2.text
import java.nio.file.Path
import scala.concurrent.duration.*

/** One run of a program: it finished with an exit code, or it took longer than allowed and was stopped. */
enum Run:
  case Done(exit: Int, output: String)
  case TimedOut(output: String)

  def ok: Boolean = this match
    case Done(0, _) => true
    case _ => false
  def output: String

object Run:
  /** A target an earlier batch built: nothing to run. */
  val built: Run = Done(0, "")

  /** Runs `command` in `dir`, killed after `timeout` or on cancel; its output (stdout and stderr by line if `merged`) kept either way. */
  def of(command: String, args: List[String], dir: Path, timeout: FiniteDuration, env: Map[String, String] = Map.empty,
      merged: Boolean = true): IO[Run] =
    Ref[IO].of(Vector.empty[String]).flatMap { out =>
      val exec = ProcessBuilder(command, args).withWorkingDirectory(fs2.io.file.Path.fromNioPath(dir)).withExtraEnv(env).spawn[IO].use { p =>
        def lines(s: fs2.Stream[IO, Byte]) = s.through(text.utf8.decode).through(text.lines)
        val read = if merged then lines(p.stdout).merge(lines(p.stderr)).evalMap(l => out.update(_ :+ l)).compile.drain
          else p.stdout.through(text.utf8.decode).evalMap(c => out.update(_ :+ c)).compile.drain &> p.stderr.compile.drain
        read *> p.exitValue
      }
      def joined(o: Vector[String]) = if merged then o.mkString("\n") else o.mkString
      exec.flatMap(code => out.get.map(o => Done(code, joined(o))))
        .timeoutTo(timeout, out.get.map(o => TimedOut(joined(o) + s"\ntimed out after ${timeout.toSeconds}s")))
    }
