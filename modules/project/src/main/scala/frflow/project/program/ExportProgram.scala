package frflow.project.program

import cats.Functor
import cats.syntax.all.*
import frflow.project.pipeline.Analysis
import frflow.project.port.{ProjectFiles, Records}
import frflow.project.report.Exports
import frflow.wire.file.Files
import frflow.wire.snapshot.Snapshot

/** `export`: the snapshot written (`.frflow/kb.json`, for tools; FrFlow never reads it back); its text, which
  * `--json` prints.
  */
final class ExportProgram[F[_]: Functor](files: ProjectFiles[F]):
  def apply(a: Analysis): F[String] =
    val text = Files.print(Snapshot.format, Exports.snapshot(a))
    files.writeIfChanged(Records.path(Snapshot.format), text).as(text)
