package frflow.project.port

import cats.Monad
import cats.syntax.all.*
import frflow.core.name.{NodeId, RelPath}
import frflow.project.pipeline.Recorded
import frflow.project.port.ProjectFiles
import frflow.proof.verdict.Checks
import frflow.testing.report.{Failure, TestReport}
import frflow.wire.check.ChecksFile
import frflow.wire.file.{FileFormat, Files}
import frflow.wire.test.TestsFile

/** The records under `.frflow/` that runs keep: the checks and the test reports (derived, not committed: one that
  * does not read is as none, and is made again), and the failing cases kept (committed).
  */
object Records:
  def read[F[_]: Monad](files: ProjectFiles[F]): F[Recorded] =
    (load(files, ChecksFile.format), load(files, TestsFile.format), load(files, TestsFile.counterexamples))
      .mapN((c, t, f) => Recorded(c.getOrElse(Checks.none), t.getOrElse(Map.empty), f.getOrElse(Map.empty)))

  def writeChecks[F[_]](files: ProjectFiles[F], checks: Checks): F[Boolean] = write(files, ChecksFile.format, checks)

  def writeTests[F[_]](files: ProjectFiles[F], tests: Map[NodeId, (String, TestReport)]): F[Boolean] =
    write(files, TestsFile.format, tests)

  def writeFailures[F[_]](files: ProjectFiles[F], kept: Map[NodeId, List[Failure]]): F[Boolean] =
    write(files, TestsFile.counterexamples, kept)

  def path(f: FileFormat[?]): RelPath = RelPath.parse(f.file).getOrElse(RelPath.fromIdentifiers(".frflow", f.file))

  private def load[F[_]: Monad, A](files: ProjectFiles[F], f: FileFormat[A]): F[Option[A]] =
    files.read(path(f)).map(_.flatMap(Files.read(f, _).toOption))

  private def write[F[_], A](files: ProjectFiles[F], f: FileFormat[A], a: A): F[Boolean] =
    files.writeIfChanged(path(f), Files.print(f, a))
