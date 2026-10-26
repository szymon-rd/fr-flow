package frflow.project.port

import frflow.decision.ledger.Ledger

/** The ledger's file under the project's lock. Interpreters: the file (a `Resource` holding the lock) and memory.
  * Laws, for both: `update(f)` stores what `f` returns only on `Right`; concurrent `update`s are serialized.
  */
trait LedgerStore[F[_]]:
  def load: F[Ledger]
  def update[E, A](f: Ledger => Either[E, (Ledger, A)]): F[Either[E, A]]

object LedgerStore:
  def file[F[_]: cats.effect.Async](path: java.nio.file.Path): cats.effect.Resource[F, LedgerStore[F]] = ???
  def inMemory[F[_]: cats.effect.Concurrent](start: Ledger): F[LedgerStore[F]] = ???
