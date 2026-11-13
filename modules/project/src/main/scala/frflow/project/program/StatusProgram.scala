package frflow.project.program

import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.project.check.Render
import frflow.project.pipeline.Analysis
import frflow.project.port.ProjectFiles

/** `status`: the Rocq written as the model now says (no Rocq run) and the snapshot exported. */
final class StatusProgram[F[_]: Monad: Parallel](files: ProjectFiles[F]):
  def apply(a: Analysis): F[Unit] = (Render(files)(a), ExportProgram(files)(a)).parTupled.void
