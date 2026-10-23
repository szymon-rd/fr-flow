package frflow
package check

import cats.effect.IO
import java.nio.charset.StandardCharsets.UTF_8
import frflow.ledger.Store
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

/** The files the checker reads and writes, as IO (read whole and written whole by the ledger's `Store`). */
object Disk:
  def read(p: Path): IO[Option[String]] = Store.read(p)

  def exists(p: Path): IO[Boolean] = IO.blocking(Files.exists(p))

  /** Writes `text` unless the file already holds it; whether it wrote. */
  def update(p: Path, text: String): IO[Boolean] =
    read(p).flatMap { now =>
      if now.contains(text) then IO.pure(false)
      else IO.blocking { Files.createDirectories(p.getParent); Files.writeString(p, text, UTF_8) }.as(true)
    }

  /** The entries of a directory, sorted; none when it is missing. */
  def list(dir: Path): IO[List[Path]] = IO.blocking {
    if !Files.isDirectory(dir) then Nil
    else scala.util.Using.resource(Files.list(dir))(_.iterator.asScala.toList).sorted
  }

  /** The regular files under a directory (following links), or the path itself when it is a file. */
  def files(p: Path): IO[List[Path]] = IO.blocking {
    if !Files.isDirectory(p) then List(p)
    else scala.util.Using.resource(Files.walk(p, java.nio.file.FileVisitOption.FOLLOW_LINKS))(_.iterator.asScala.filter(Files.isRegularFile(_)).toList)
  }

  def isDirectory(p: Path): IO[Boolean] = IO.blocking(Files.isDirectory(p))
  def isFile(p: Path): IO[Boolean] = IO.blocking(Files.isRegularFile(p))
  def delete(p: Path): IO[Unit] = IO.blocking(Files.deleteIfExists(p)).void
