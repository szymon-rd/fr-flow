package crm

import cats.effect.{IO, Ref}

/** The CRM's database in memory, its own code for development and tests: the three tables and the event log, each
  * in the order its rows were stored; a variant of the database's Scala, tested against `databaseModel` as SQLite
  * is.
  */
final class MemoryDatabase private (held: Ref[IO, Tables], keepsShares: Boolean):
  def load: IO[CrmStore] = held.get.map(_.store)
  def storeAbout(id: BigInt, t: CrmStore): IO[Unit] = held.update { h =>
    val s = h.store
    val kept = if keepsShares then s.shares.filter(_.record == id) else Nil
    h.copy(store = CrmStore(s.records.filterNot(_.id == id) ++ t.records.filter(_.id == id),
      s.shares.filterNot(_.record == id) ++ (kept ++ t.shares.filter(_.record == id)).distinct,
      s.expiries.filterNot(_.record == id) ++ t.expiries.filter(_.record == id)))
  }
  def logEvent(e: Event): IO[Unit] = held.update(h => h.copy(events = h.events :+ e))
  def tables: IO[Tables] = held.get

object MemoryDatabase:
  /** A database in memory holding the tables; `keepsShares`, the seeded bug, keeps a record's old shares when it
    * stores the record again.
    */
  def holding(t: Tables, keepsShares: Boolean = false): IO[MemoryDatabase] =
    Ref[IO].of(t).map(MemoryDatabase(_, keepsShares))
