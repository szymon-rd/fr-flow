package frflow
package ledger
package store

import cats.effect.std.Mutex
import cats.effect.{IO, Resource}
import cats.syntax.all.*
import java.nio.channels.FileChannel
import java.nio.file.{Files, Path, StandardOpenOption}

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
