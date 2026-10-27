package frflow.project.port

import cats.effect.std.Mutex
import cats.effect.{Concurrent, Ref}
import cats.syntax.all.*
import frflow.decision.ledger.Ledger

/** The ledger in memory, its updates serialized: the decision programs tested without a file. */
final class MemoryLedger[F[_]: Concurrent] private (held: Ref[F, Ledger], mutex: Mutex[F]) extends LedgerStore[F]:
  def load: F[Ledger] = held.get

  def update[E, A](f: Ledger => Either[E, (Ledger, A)]): F[Either[E, A]] =
    mutex.lock.surround(held.get.flatMap(before => f(before).traverse((after, a) => held.set(after).as(a))))

object MemoryLedger:
  def apply[F[_]: Concurrent](start: Ledger): F[MemoryLedger[F]] =
    (Ref.of[F, Ledger](start), Mutex[F]).mapN(new MemoryLedger(_, _))
