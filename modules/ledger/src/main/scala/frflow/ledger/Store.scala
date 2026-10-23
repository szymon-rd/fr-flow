package frflow
package ledger

import cats.effect.{IO, Resource}
import cats.effect.std.Mutex
import cats.syntax.all.*
import io.circe.{Decoder, Encoder, Json}
import io.circe.parser.decode
import io.circe.syntax.*
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption, StandardOpenOption}
import scala.util.control.NoStackTrace

/** What fails reading or writing the ledger module's files: raised in `IO`, mapped once at each edge. */
enum LedgerError(message: String) extends Exception(message) with NoStackTrace:
  /** FrFlow does not guess what the file held. */
  case BadFile(path: Path, reason: String) extends LedgerError(s"$path does not read: $reason")
  case BadKey(path: Path, reason: String) extends LedgerError(s"the signing key $path does not read: $reason")

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

/** One writer at a time for a file: the fibers of this process, then other processes (through `file.lock` beside it).
  * Make one per file and share it: two in one process would refuse each other's lock.
  */
final class FileLock private (lockFile: Path, mutex: Mutex[IO]):
  private val channel: Resource[IO, FileChannel] = Resource.fromAutoCloseable(IO.blocking {
    Files.createDirectories(lockFile.toAbsolutePath.getParent)
    FileChannel.open(lockFile, StandardOpenOption.CREATE, StandardOpenOption.WRITE)
  })
  private val held: Resource[IO, Unit] =
    mutex.lock >> channel.flatMap(ch => Resource.make(IO.blocking(ch.lock()))(l => IO.blocking(l.release())).void)
  def surround[A](io: IO[A]): IO[A] = held.surround(io)

object FileLock:
  def of(file: Path): IO[FileLock] = Mutex[IO].map(FileLock(file.resolveSibling(s"${file.getFileName}.lock"), _))

/** A JSON file changed under its lock: `update` sees it as on disk, and a refusal writes nothing. */
final class JsonStore[A: Encoder: Decoder] private (file: Path, empty: A, lock: FileLock):
  /** The file decoded, or `empty` when there is none; a file that does not read is a `BadFile`. */
  def load: IO[A] = Store.read(file).flatMap(_.fold(IO.pure(empty))(text =>
    IO.fromEither(decode[A](text).leftMap(e => LedgerError.BadFile(file, e.getMessage)))))
  def update[E, B](f: A => Either[E, (A, B)]): IO[Either[E, B]] =
    lock.surround(load.flatMap(f(_).traverse((next, b) => Store.writeJson(file, next.asJson).as(b))))

object JsonStore:
  def make[A: Encoder: Decoder](file: Path, empty: A): IO[JsonStore[A]] = FileLock.of(file).map(new JsonStore(file, empty, _))
