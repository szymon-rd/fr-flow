package frflow.project.port.memory

import cats.effect.{Concurrent, Ref}
import cats.syntax.all.*
import frflow.decision.ledger.Ledger
import frflow.project.port.LedgerStore

/** The ledger in memory, each update one atomic change of a `Ref`: the decision programs tested without a file. */
final class MemoryLedger[F[_]: Concurrent] private (held: Ref[F, Ledger]) extends LedgerStore[F]:
  def load: F[Ledger] = held.get

  def update[E, A](f: Ledger => Either[E, (Ledger, A)]): F[Either[E, A]] =
    held.modify(before => f(before).fold(e => (before, Left(e)), (after, a) => (after, Right(a))))

object MemoryLedger:
  def apply[F[_]: Concurrent](start: Ledger): F[MemoryLedger[F]] = Ref.of[F, Ledger](start).map(new MemoryLedger(_))
