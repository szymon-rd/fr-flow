package frflow
package ledger

import cats.effect.IO
import cats.syntax.all.*
import frflow.protocol.*
import io.circe.syntax.*
import java.nio.file.Path

/** The ledger in `.frflow/ledger.json`: read whole; changed under its lock, all or nothing. */
trait LedgerStore:
  def load: IO[Ledger]
  /** Applies `f` to the ledger as it is on disk, under the lock; writes what it returns, or nothing if it
    * refuses.
    */
  def update[A](f: Ledger => Either[Refusal, (Ledger, A)]): IO[Either[Refusal, A]]
  def save(l: Ledger): IO[Unit] = update(_ => Right(l -> ())).void

object LedgerStore:
  /** The store of `file`; one per file in a process (see `FileLock`). */
  def make(file: Path): IO[LedgerStore] = FileLock.of(file).map { lock =>
    new LedgerStore:
      def load: IO[Ledger] = Store.load(file, Ledger.empty)
      def update[A](f: Ledger => Either[Refusal, (Ledger, A)]): IO[Either[Refusal, A]] =
        lock.surround(load.flatMap(l => f(l).traverse((next, a) => Store.writeJson(file, next.asJson).as(a))))
  }

/** The developer's requests in `.frflow/requests.json`, and the agent's answers. */
trait RequestStore:
  def load: IO[List[Request]]
  /** The developer asks for a change, on a node or on the idea. */
  def ask(node: Option[NodeId], text: String, by: String): IO[Request]
  /** Answers the request `to`, or the open request on the node `to` (see `Requests.answer`). */
  def answer(to: String, text: String, isNode: NodeId => Boolean): IO[Either[Refusal, Request]]
  def close(id: RequestId): IO[Either[Refusal, Request]]

object RequestStore:
  /** The store of `file`; one per file in a process (see `FileLock`). */
  def make(file: Path): IO[RequestStore] = FileLock.of(file).map { lock =>
    new RequestStore:
      def load: IO[List[Request]] = Store.load(file, List.empty[Request])
      private def change[E, A](f: (List[Request], java.time.Instant) => Either[E, (List[Request], A)]): IO[Either[E, A]] =
        lock.surround(for
          rs  <- load
          now <- IO.realTimeInstant
          out <- f(rs, now).traverse((next, a) => Store.writeJson(file, next.asJson).as(a))
        yield out)
      def ask(node: Option[NodeId], text: String, by: String): IO[Request] =
        change[Nothing, Request]((rs, now) => Right(Requests.ask(rs, node, text, by, now))).map(_.merge)
      def answer(to: String, text: String, isNode: NodeId => Boolean): IO[Either[Refusal, Request]] =
        change(Requests.answer(_, to, text, isNode, _))
      def close(id: RequestId): IO[Either[Refusal, Request]] = change((rs, _) => Requests.close(rs, id))
  }
