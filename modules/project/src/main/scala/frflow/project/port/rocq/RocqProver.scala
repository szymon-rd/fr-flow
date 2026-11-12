package frflow.project.port.rocq

import cats.data.NonEmptyList
import cats.effect.std.Mutex
import cats.effect.{Async, Ref, Resource}
import cats.syntax.all.*
import fs2.io.process.Processes
import frflow.decision.content.Sha
import frflow.project.port.Prover
import frflow.project.process.{Command, Exited}
import frflow.proof.lean.ast.ModuleName
import frflow.proof.reading.{RocqReport, RocqSource}
import frflow.proof.rocq.RocqProject
import frflow.proof.verdict.ProverRun
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}
import scala.concurrent.duration.FiniteDuration

/** Rocq in the project's `rocq/`: a build compiles each module asked after every module it imports (FrFlow's
  * library, the generated modules, the developer's proofs), each only when what it was last compiled from changed
  * (`RocqCache`), and none whose imports did not go through whole. Builds write `rocq/_build/`, so one runs at a
  * time.
  */
object RocqProver:
  /** In `rocqDir` (the project's `rocq/`, made if missing), FrFlow's library in `library` (`FrFlow/Base.v` in it). */
  def make[F[_]: Async: Processes](rocqDir: Path, library: Path, rocq: Command): Resource[F, Prover[F]] =
    Resource.eval(Async[F].blocking(Files.createDirectories(rocqDir)) >> Mutex[F])
      .map(Live(RocqDirs(rocqDir, library), rocq, _))

  /** How a module is built and what is kept of it: a change to it builds every module again. */
  val Version: String = "1"

  /** How long `rocq --version` may take. */
  val Probe: FiniteDuration = FiniteDuration(30, "seconds")

  private final class Live[F[_]: Async: Processes](dirs: RocqDirs, rocq: Command, building: Mutex[F])
      extends Prover[F]:
    private val (compiler, cache) = (RocqCompiler(dirs, rocq), RocqCache(dirs))
    private type Done = Ref[F, Map[String, RocqBuilt]]

    private def version: F[Exited] = Command.run(rocq.copy(timeout = Probe), List("--version"), dirs.project, Map.empty)
    def available: F[Boolean] = version.map(_.ok).handleError(_ => false)

    def build(targets: NonEmptyList[ModuleName]): F[ProverRun] = building.lock.surround(
      (version.map(_.output), Ref.of[F, Map[String, RocqBuilt]](Map.empty)).flatMapN { (v, done) =>
        targets.toList.map(RocqProject.logical).traverse(built(_, v, done)).flatMap { asked =>
          done.get.map { all =>
            val report = RocqReport.print(all.values.toList.flatMap(_.said).sortBy(_.path))
            if all.values.exists(_.timedOut) then ProverRun.TimedOut(report)
            else if asked.forall(_.whole) then ProverRun.Built(report)
            else ProverRun.Failed(report)
          }
        }
      })

    /** A module built, once in a build: after what it imports, and not at all when one of those is not whole. */
    private def built(logical: String, version: String, done: Done): F[RocqBuilt] =
      done.get.map(_.get(logical)).flatMap(_.fold(
        // held while its imports are built, so a module importing itself, however far, ends
        done.update(_.updated(logical, RocqBuilt("", None, false))) >>
          read(logical).flatMap(_.fold(missing(logical).pure[F])(compiled(logical, _, version, done)))
            .flatTap(b => done.update(_.updated(logical, b))))(_.pure[F]))

    private def compiled(logical: String, text: String, version: String, done: Done): F[RocqBuilt] =
      RocqSource.imports(text).filter(dirs.source(_).isDefined).traverse(built(_, version, done)).flatMap { imported =>
        val inputs = Sha.parts((RocqProver.Version :: version :: logical :: text :: imported.map(_.stamp))*)
        if !imported.forall(_.whole) then RocqBuilt("", None, imported.exists(_.timedOut)).pure[F]
        else cache.read(logical, inputs).flatMap(_.fold(
          compiler(logical, dirs.source(logical).get, text).flatMap(_.fold(RocqBuilt("", None, true).pure[F])(
            cache.write(logical, inputs, _))))(_.pure[F]))
      }

    private def read(logical: String): F[Option[String]] = Async[F].blocking(
      dirs.source(logical).filter(Files.isRegularFile(_)).map(Files.readString(_, UTF_8)))

    private def missing(logical: String): RocqBuilt =
      RocqBuilt("", Some(RocqReport.File(RocqDirs.file(logical), Map.empty, Map.empty, Some("there is no such file"))),
        false)
