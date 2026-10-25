package frflow
package ledger
package store

import cats.effect.IO
import cats.syntax.all.*
import io.circe.parser.decode
import io.circe.syntax.*
import io.circe.{Decoder, Encoder}
import java.nio.file.Path

/** A JSON file changed under its lock: `update` sees it as on disk, and a refusal writes nothing. `print` is the
  * file's text.
  */
final class JsonStore[A: Decoder] private (file: Path, empty: A, print: A => String, lock: FileLock):
  /** The file decoded, or `empty` when there is none; a file that does not read is a `BadFile`. */
  def load: IO[A] = Store.read(file).flatMap(_.fold(IO.pure(empty))(text =>
    IO.fromEither(decode[A](text).leftMap(e => LedgerError.BadFile(file, e.getMessage)))))
  def update[E, B](f: A => Either[E, (A, B)]): IO[Either[E, B]] =
    lock.surround(load.flatMap(f(_).traverse((next, b) => Store.write(file, print(next)).as(b))))

object JsonStore:
  def make[A: Encoder: Decoder](file: Path, empty: A): IO[JsonStore[A]] =
    make(file, empty, a => frflow.protocol.Canonical.file(a.asJson) + "\n")
  def make[A: Decoder](file: Path, empty: A, print: A => String): IO[JsonStore[A]] =
    FileLock.of(file).map(new JsonStore(file, empty, print, _))
  /** The ledger, written as `Ledger.file` writes it. */
  def ledger(file: Path): IO[JsonStore[frflow.protocol.Ledger]] =
    make(file, frflow.protocol.Ledger.empty, frflow.protocol.Ledger.file)
