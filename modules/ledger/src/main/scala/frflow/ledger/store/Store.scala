package frflow
package ledger
package store

import cats.effect.IO
import io.circe.Json
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption}

/** FrFlow's files: read whole, and written whole then moved into place, so a reader never sees half a file. */
object Store:
  def read(file: Path): IO[Option[String]] =
    IO.blocking(Option.when(Files.isRegularFile(file))(Files.readString(file, UTF_8)))

  def write(file: Path, text: String): IO[Unit] = IO.blocking {
    val dir = file.toAbsolutePath.getParent
    Files.createDirectories(dir)
    val tmp = Files.createTempFile(dir, s".${file.getFileName}", ".tmp")
    Files.writeString(tmp, text, UTF_8)
    Files.move(tmp, file, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
  }.void

  def writeJson(file: Path, json: Json): IO[Unit] = write(file, frflow.protocol.Canonical.file(json) + "\n")
