package frflow
package ledger
package signing

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.protocol.*
import java.nio.file.attribute.PosixFilePermissions
import java.nio.file.{Files, Path, Paths}
import java.security.PublicKey
import scala.jdk.CollectionConverters.*

/** The keys on disk: the developer's signing key, outside the repository (which others may edit), and the project's
  * public keys in `.frflow/keys/NAME.pub`, committed.
  */
final class KeyStore private (keyFile: Path, keysDir: Path):
  /** The developer's key, created on first use, readable by its owner only (where the file system has permissions). */
  def developer: IO[DeveloperKey] = IO.blocking(Files.isRegularFile(keyFile)).ifM(read, create)

  private def read = IO.blocking(Files.readString(keyFile)).flatMap(text =>
    IO.fromEither(Keys.decode(text).leftMap(LedgerError.BadKey(keyFile, _))))

  private def create = IO(Keys.generate()).flatTap(k => IO.blocking {
    Files.createDirectories(keyFile.toAbsolutePath.getParent)
    val posix = keyFile.getFileSystem.supportedFileAttributeViews.contains("posix")
    val ownerOnly = if posix then List(PosixFilePermissions.asFileAttribute(PosixFilePermissions.fromString("rw-------"))) else Nil
    Files.createFile(keyFile, ownerOnly*)
    Files.writeString(keyFile, Keys.encode(k))
  })

  /** The name the developer's key is filed under (`NAME.pub`), if the key exists and is filed. */
  def filedName: IO[Option[String]] =
    IO.blocking(Files.isRegularFile(keyFile)).ifM(
      (read, KeyStore.filed(keysDir)).mapN((k, all) => all.collectFirst { case (name, pub) if Keys.id(pub) == k.id => name }),
      IO.pure(None))

  /** Files the public key as `NAME.pub` (`ID.pub` with no name), unless it is there under any name. */
  def publish(key: PublicKey, name: String): IO[Unit] =
    KeyStore.projectKeys(keysDir).flatMap { known =>
      val file = keysDir.resolve(s"${if name.trim.isEmpty then Keys.id(key).value else name.trim}.pub")
      Store.write(file, Keys.encodePublic(key)).unlessA(known.contains(Keys.id(key)))
    }

object KeyStore:
  /** `FRFLOW_KEY`, or `~/.config/frflow/signing.key`. */
  def keyFile(env: Map[String, String], home: Path): Path =
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).fold(home.resolve(".config/frflow/signing.key"))(Paths.get(_))

  def at(keyFile: Path, keysDir: Path): KeyStore = new KeyStore(keyFile, keysDir)

  def projectKeys(keysDir: Path): IO[Map[KeyId, PublicKey]] = filed(keysDir).map(_.map((_, pub) => Keys.id(pub) -> pub).toMap)

  /** Every `.pub` in `keysDir` that reads: its name (the file's, without `.pub`), and the key. */
  private def filed(keysDir: Path): IO[List[(String, PublicKey)]] =
    val pubs = Resource.fromAutoCloseable(IO.blocking(Files.list(keysDir)))
      .use(files => IO.blocking(files.iterator.asScala.toList.filter(_.toString.endsWith(".pub")).sortBy(_.toString)))
    IO.blocking(Files.isDirectory(keysDir)).ifM(pubs, IO.pure(Nil)).flatMap(_.traverseFilter(f =>
      IO.blocking(Files.readString(f).linesIterator.map(_.trim).find(_.nonEmpty).flatMap(Keys.decodePublic(_).toOption)
        .map(f.getFileName.toString.stripSuffix(".pub") -> _))))
