package frflow
package ledger

import cats.effect.{IO, Resource}
import cats.syntax.all.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}
import java.nio.file.attribute.PosixFilePermissions
import java.security.PublicKey
import scala.jdk.CollectionConverters.*

/** The keys on disk: the developer's signing key, outside the repository the agent edits, and the
  * project's public keys in `.frflow/keys/NAME.pub`, committed.
  */
trait KeyStore:
  /** The developer's key, created on first use (readable by its owner only). */
  def developer: IO[DeveloperKey]
  /** The project's developer keys, by id: every `.pub` in its keys directory that reads. */
  def projectKeys: IO[Map[KeyId, PublicKey]]
  /** Files the public key as `NAME.pub` (`ID.pub` with no name), unless it is there under any name. */
  def publish(key: PublicKey, name: String): IO[Unit]

object KeyStore:

  /** Where the developer's key is: `FRFLOW_KEY`, or `~/.config/frflow/signing.key`. */
  def keyFile(env: Map[String, String], home: Path): Path =
    env.get("FRFLOW_KEY").map(_.trim).filter(_.nonEmpty).fold(home.resolve(".config/frflow/signing.key"))(Paths.get(_))

  /** The store for a project's `keysDir` (`.frflow/keys`), with the developer's key where the
    * environment says.
    */
  def default(keysDir: Path): IO[KeyStore] =
    IO(keyFile(sys.env, Paths.get(sys.props.getOrElse("user.home", ".")))).map(at(_, keysDir))

  /** The developer keys in `keysDir`: every `.pub` in it that reads, by its id. */
  def projectKeys(keysDir: Path): IO[Map[KeyId, PublicKey]] =
    val pubs = Resource.fromAutoCloseable(IO.blocking(Files.list(keysDir)))
      .use(files => IO.blocking(files.iterator.asScala.toList.filter(_.toString.endsWith(".pub")).sortBy(_.toString)))
    IO.blocking(Files.isDirectory(keysDir)).ifM(pubs, IO.pure(Nil)).flatMap(_.traverseFilter(f =>
      IO.blocking(Files.readString(f).linesIterator.map(_.trim).find(_.nonEmpty).flatMap(Keys.decodePublic(_).toOption))))
      .map(_.map(pub => Keys.id(pub) -> pub).toMap)

  def at(keyFile: Path, keysDir: Path): KeyStore = new KeyStore:
    def developer: IO[DeveloperKey] =
      IO.blocking(Files.isRegularFile(keyFile)).ifM(read, create)

    private def read = IO.blocking(Files.readString(keyFile)).flatMap(text =>
      IO.fromEither(Keys.decode(text).leftMap(LedgerError.BadKey(keyFile, _))))

    // Created readable by its owner only, where the file system has permissions.
    private def create = IO(Keys.generate()).flatTap(k => IO.blocking {
      Files.createDirectories(keyFile.toAbsolutePath.getParent)
      val posix = keyFile.getFileSystem.supportedFileAttributeViews.contains("posix")
      val ownerOnly = if posix then List(PosixFilePermissions.asFileAttribute(PosixFilePermissions.fromString("rw-------"))) else Nil
      Files.createFile(keyFile, ownerOnly*)
      Files.writeString(keyFile, Keys.encode(k))
    })

    def projectKeys: IO[Map[KeyId, PublicKey]] = KeyStore.projectKeys(keysDir)

    def publish(key: PublicKey, name: String): IO[Unit] =
      projectKeys.flatMap { known =>
        val file = keysDir.resolve(s"${if name.trim.isEmpty then Keys.id(key).value else name.trim}.pub")
        Store.write(file, Keys.encodePublic(key)).unlessA(known.contains(Keys.id(key)))
      }
