package frflow.project.port

import cats.effect.std.Mutex
import cats.effect.{Async, Resource}
import cats.syntax.all.*
import frflow.decision.ledger.Ledger
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.LedgerFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption, StandardOpenOption}

/** The ledger's file under the project's lock. Interpreters: the file (`file`), and memory (`MemoryLedger`). Laws,
  * for both: `update(f)` stores what `f` returns only on `Right`, and `load` then gives it; concurrent `update`s are
  * serialized, each on the ledger the one before stored.
  */
trait LedgerStore[F[_]]:
  def load: F[Ledger]
  def update[E, A](f: Ledger => Either[E, (Ledger, A)]): F[Either[E, A]]

object LedgerStore:
  /** `.frflow/ledger.json` under `root`: none there reads as the empty ledger, one that does not read is raised
    * (`FrFlowError.NotRead`). An update holds the process's lock and the file's (`ledger.lock` beside it, so a CLI
    * and a web view deciding at once take turns), and replaces the file whole.
    */
  def file[F[_]: Async](root: Path): Resource[F, LedgerStore[F]] =
    val path = root.resolve(LedgerFile.format.file)
    Resource.eval(Mutex[F]).map(mutex => new LedgerStore[F]:
      def load: F[Ledger] = Async[F].blocking(Option.when(Files.isRegularFile(path))(Files.readString(path, UTF_8)))
        .flatMap(_.fold(Ledger.empty.pure[F])(t => Wire.read(LedgerFile.format, t).leftMap(FrFlowError.NotRead(_))
          .liftTo[F]))

      def update[E, A](f: Ledger => Either[E, (Ledger, A)]): F[Either[E, A]] =
        mutex.lock.surround(locked(path).surround(load.flatMap(before => f(before).traverse((after, a) =>
          store(path, after).as(a)))))
    )

  private def locked[F[_]: Async](ledger: Path): Resource[F, Unit] =
    Resource.make(Async[F].blocking {
      val _ = Files.createDirectories(ledger.toAbsolutePath.getParent)
      val channel = FileChannel.open(ledger.resolveSibling("ledger.lock"), StandardOpenOption.CREATE,
        StandardOpenOption.WRITE)
      (channel, channel.lock())
    })((channel, lock) => Async[F].blocking { lock.release(); channel.close() }).void

  private def store[F[_]: Async](path: Path, l: Ledger): F[Unit] = Async[F].blocking {
    val written = Files.writeString(path.resolveSibling("ledger.json.writing"), Wire.print(LedgerFile.format, l), UTF_8)
    val _ = Files.move(written, path, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
  }
