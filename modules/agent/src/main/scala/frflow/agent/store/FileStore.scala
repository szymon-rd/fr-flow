package frflow.agent.store

import cats.effect.std.Mutex
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import io.circe.parser.decode
import io.circe.syntax.*
import io.circe.{Decoder, Encoder}
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption, StandardOpenOption}

/** A store in a JSON file of the project: none there reads as `empty`; one that does not read is raised (the agent's
  * files are its own: FrFlow never reads them). An update holds the process's lock and the file's (`NAME.lock`
  * beside it, so a CLI and a web view take turns), and replaces the file whole.
  */
object FileStore:
  def make[F[_]: Async, A: Encoder: Decoder](path: Path, empty: A): F[Store[F, A]] =
    Mutex[F].map(mutex => new Store[F, A]:
      def load: F[A] = Async[F].blocking(Option.when(Files.isRegularFile(path))(Files.readString(path, UTF_8)))
        .flatMap(_.fold(empty.pure[F])(t => decode[A](t).leftMap(e =>
          IllegalStateException(s"$path does not read: ${e.getMessage}")).liftTo[F]))

      def update[E, B](f: A => Either[E, (A, B)]): F[Either[E, B]] =
        mutex.lock.surround(locked(path).surround(load.flatMap(a => f(a).traverse((next, b) => store(next).as(b)))))

      private def store(a: A): F[Unit] = Async[F].blocking {
        val _ = Files.createDirectories(path.toAbsolutePath.getParent)
        val written = Files.writeString(path.resolveSibling(s"${path.getFileName}.writing"),
          a.asJson.spaces2 + "\n", UTF_8)
        val _ = Files.move(written, path, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
      }
    )

  private def locked[F[_]: Async](path: Path): Resource[F, Unit] =
    Resource.make(Async[F].blocking {
      val _ = Files.createDirectories(path.toAbsolutePath.getParent)
      val channel = FileChannel.open(path.resolveSibling(s"${path.getFileName}.lock"), StandardOpenOption.CREATE,
        StandardOpenOption.WRITE)
      (channel, channel.lock())
    })((channel, lock) => Async[F].blocking { lock.release(); channel.close() }).void
