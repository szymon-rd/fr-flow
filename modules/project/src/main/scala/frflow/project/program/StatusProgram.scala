package frflow.project.program

import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.project.check.Render
import frflow.project.pipeline.Analysis
import frflow.project.port.ProjectFiles
import frflow.project.report.Review

/** `status`: the Rocq written as the model now says (no Rocq run) and the snapshot exported; then the review as it
  * stands, with the decisions that do not count.
  */
final class StatusProgram[F[_]: Monad: Parallel](files: ProjectFiles[F]):
  def apply(a: Analysis): F[Review] =
    (Render(files)(a), ExportProgram(files)(a)).parTupled.as(Review.of(a))
