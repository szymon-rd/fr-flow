package frflow.project.port

import frflow.core.name.RelPath

/** The project's files. Interpreters: the disk and memory. Laws, for both: a read after a write gives what was
  * written; `writeIfChanged` writes nothing, and says so, when the file already holds the text.
  */
trait ProjectFiles[F[_]]:
  def read(p: RelPath): F[Option[String]]
  def list(dir: RelPath): F[List[RelPath]]
  def writeIfChanged(p: RelPath, text: String): F[Boolean]
  def delete(p: RelPath): F[Unit]

object ProjectFiles:
  /** Over the project's directory: blocking file I/O. */
  def make[F[_]: cats.effect.Sync](root: java.nio.file.Path): ProjectFiles[F] = ???
