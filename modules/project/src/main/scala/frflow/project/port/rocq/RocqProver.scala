package frflow.project.port.rocq

import cats.data.NonEmptyList
import cats.effect.std.{Mutex, Semaphore}
import cats.effect.{Async, Ref, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.decision.content.Sha
import frflow.project.port.Prover
import frflow.project.process.{Command, Exited}
import frflow.proof.prover.ast.ModuleName
import frflow.proof.reading.{RocqReport, RocqSource}
import frflow.proof.rocq.RocqProject
import frflow.proof.verdict.ProverRun
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.concurrent.duration.FiniteDuration

/** Rocq in the project's `rocq/`: a build compiles each module asked after every module it imports (FrFlow's
  * library, the generated modules, the developer's proofs), each only when what it was last compiled from changed
  * (`RocqCache`), and none whose imports did not go through whole. Builds run at once: a module is compiled by one
  * of them at a time (the next finds it compiled), and no more compiles run than the tool allows (`RocqTool.jobs`).
  * A module of tries (`RocqProject.tries`) is compiled again only when what it states changed: its text, or that of
  * a module of the project it imports. A change to FrFlow's library, or to what its imports compile to, does not
  * try it again; removing `rocq/_build/` does.
  */
object RocqProver:
  /** In `rocqDir` (the project's `rocq/`, made if missing), FrFlow's library in `library` (`FrFlow/Base.v` in it). */
  def make[F[_]: Async: Processes](rocqDir: Path, library: Path, rocq: RocqTool): Resource[F, Prover[F]] =
    Resource.eval(Async[F].blocking(Files.createDirectories(rocqDir)) >>
      (Ref.of[F, Map[String, Mutex[F]]](Map.empty), Semaphore[F](rocq.jobs.max(1).toLong)).tupled)
      .map((locks, running) => Live(RocqDirs(rocqDir, library), rocq, Turns(locks, running)))

  /** Who compiles: one build at a time each module, and at most as many compiles at once as there are permits. */
  private final class Turns[F[_]: Async](locks: Ref[F, Map[String, Mutex[F]]], running: Semaphore[F]):
    def of[A](logical: String)(cachedOrCompiled: F[A] => F[A])(compile: F[A]): F[A] =
      Mutex[F].flatMap(fresh => locks.modify(all => all.get(logical).fold((all.updated(logical, fresh), fresh))(m =>
        (all, m)))).flatMap(_.lock.surround(cachedOrCompiled(running.permit.surround(compile))))

  /** How a module is built and what is kept of it: a change to it builds every module again. */
  val Version: String = "1"

  /** How long `rocq --version` may take. */
  val Probe: FiniteDuration = FiniteDuration(30, "seconds")

  private final class Live[F[_]: Async: Processes](dirs: RocqDirs, rocq: RocqTool, turns: Turns[F])
      extends Prover[F]:
    private val (compiler, cache) = (RocqCompiler(dirs, rocq), RocqCache(dirs))
    private type Done = Ref[F, Map[String, RocqBuilt]]

    private def version: F[Exited] =
      Command.run(rocq.command.copy(timeout = Probe), List("--version"), dirs.project, Map.empty)
    def available: F[Boolean] = version.map(_.ok).handleError(_ => false)

    def build(targets: NonEmptyList[ModuleName]): F[ProverRun] =
      (version.map(_.output), Ref.of[F, Map[String, RocqBuilt]](Map.empty)).flatMapN { (v, done) =>
        targets.toList.map(RocqProject.logical).traverse(built(_, v, done)).flatMap { asked =>
          done.get.map { all =>
            val report = RocqReport.print(all.values.toList.flatMap(_.said).sortBy(_.path))
            if all.values.exists(_.timedOut) then ProverRun.TimedOut(report)
            else if asked.forall(_.whole) then ProverRun.Built(report)
            else ProverRun.Failed(report)
          }
        }
      }

    /** A module built, once in a build: after what it imports, and not at all when one of those is not whole. */
    private def built(logical: String, version: String, done: Done): F[RocqBuilt] =
      done.get.map(_.get(logical)).flatMap(_.fold(
        // held while its imports are built, so a module importing itself, however far, ends
        done.update(_.updated(logical, RocqBuilt("", None, false, ""))) >>
          read(logical).flatMap(_.fold(missing(logical).pure[F])((source, text) =>
            compiled(Read(logical, source, text), version, done)))
            .flatTap(b => done.update(_.updated(logical, b))))(_.pure[F]))

    /** A module's source as a build read it. */
    private final case class Read(logical: String, source: Path, text: String)

    private def compiled(m: Read, version: String, done: Done): F[RocqBuilt] =
      val followed = RocqSource.imports(m.text).filter(dirs.source(_).isDefined)
      followed.traverse(built(_, version, done)).flatMap { imported =>
        val stated = if RocqDirs.ofLibrary(m.logical) then ""
          else Sha.parts((m.logical :: m.text :: imported.map(_.stated))*)
        val inputs = if RocqProject.tries(m.logical) then Sha.parts(RocqProver.Version, version, "tries", stated)
          else Sha.parts((RocqProver.Version :: version :: m.logical :: m.text :: imported.map(_.stamp))*)
        val compile = compiler(m.logical, m.source, m.text).flatMap(_.fold(RocqBuilt("", None, true, "").pure[F])(
          cache.write(m.logical, inputs, _)))
        val result = if !imported.forall(_.whole) then RocqBuilt("", None, imported.exists(_.timedOut), "").pure[F]
          else turns.of[RocqBuilt](m.logical)(run => cache.read(m.logical, inputs).flatMap(_.fold(run)(_.pure[F])))(
            compile)
        result.map(_.copy(stated = stated))
      }

    private def read(logical: String): F[Option[(Path, String)]] = Async[F].blocking(
      dirs.source(logical).filter(Files.isRegularFile(_)).map(p => p -> Files.readString(p, UTF_8)))

    private def missing(logical: String): RocqBuilt =
      RocqBuilt("", Some(RocqReport.File(RocqDirs.file(logical), Map.empty, Map.empty, Some("there is no such file"))),
        false, "")
