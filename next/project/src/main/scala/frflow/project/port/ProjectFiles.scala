package frflow.project.port

import cats.effect.Sync
import cats.syntax.all.*
import frflow.core.name.RelPath
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{FileVisitOption, Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The project's files, each named relative to the project and read and written whole, as UTF-8. Interpreters: the
  * disk (`make`) and memory (`MemoryFiles`). Laws, for both: a read after `writeIfChanged(p, t)` gives `t`;
  * `writeIfChanged` writes nothing, and says so, when the file already holds the text; `list(d)` gives every file
  * under `d`, sorted, and none when there is no such directory; a read after `delete` gives none.
  */
trait ProjectFiles[F[_]]:
  def read(p: RelPath): F[Option[String]]
  def list(dir: RelPath): F[List[RelPath]]
  def writeIfChanged(p: RelPath, text: String): F[Boolean]
  def delete(p: RelPath): F[Unit]

object ProjectFiles:
  /** Over the project's directory: blocking file I/O. */
  def make[F[_]: Sync](root: Path): ProjectFiles[F] = new ProjectFiles[F]:
    private def at(p: RelPath): Path = root.resolve(p.value)

    def read(p: RelPath): F[Option[String]] =
      Sync[F].blocking(Option.when(Files.isRegularFile(at(p)))(Files.readString(at(p), UTF_8)))

    def list(dir: RelPath): F[List[RelPath]] = Sync[F].blocking(
      if !Files.isDirectory(at(dir)) then Nil
      else Using.resource(Files.walk(at(dir), FileVisitOption.FOLLOW_LINKS))(_.iterator.asScala
        .filter(Files.isRegularFile(_)).map(f => root.relativize(f).toString.replace('\\', '/')).toList)
        .flatMap(RelPath.parse(_).toOption).sorted)

    def writeIfChanged(p: RelPath, text: String): F[Boolean] = read(p).flatMap(now =>
      if now.contains(text) then false.pure[F]
      else Sync[F].blocking {
        val _ = Files.createDirectories(at(p).toAbsolutePath.getParent)
        Files.writeString(at(p), text, UTF_8)
      }.as(true))

    def delete(p: RelPath): F[Unit] = Sync[F].blocking(Files.deleteIfExists(at(p))).void
