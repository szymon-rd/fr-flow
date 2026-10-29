package crm

import cats.effect.IO
import frflow.*

// ============================================================================
// The database, as proven code sees it: its operations, Definitions, and their model
// ============================================================================

/** The records, shares and expiries the database holds. */
val load = Definition[Program[CrmStore]]("the records, shares and expiries the database holds")
/** Holds what a store holds about a record in place of what the database held about it. */
val storeAbout = Definition[(BigInt, CrmStore) => Program[Unit]](
  "what a store holds about a record, held in place of what the database held about it")
/** Appends an event to the event log. */
val logEvent = Definition[Event => Program[Unit]]("an event appended to the event log")

/** What the database holds: the store, and the event log. */
final case class Tables(store: CrmStore, events: List[Event]) derives LeanType

/** The database as the proofs see it. */
object databaseModel
    extends StateModel[Tables]("the SQLite database the CRM keeps its records, shares, expiries and event log in"):
  load.means(state.get.map(t => t.store))
  storeAbout.means((id, s) => state.update(t => make[Tables](replaceAbout(t.store, id, aboutRecord(s, id)), t.events)))
  logEvent.means(e => state.update(t => make[Tables](t.store, t.events :+ e)))

val tablesModel = Node.assumption("Nothing but the CRM's programs changes the store and the event log the database " +
    "holds.")(
  databaseModel.onlyCodeChanges)

val runsOneAtATime = Node.assumption("Runs on the database never interleave: the expiry job holds the database's " +
    "lock during a run, and the write side saves one write at a time.")(
  databaseModel.atomic)

val tablesStartEmpty = Node.assumption("The database starts with no record, share or expiry, and an empty event " +
    "log.")(
  databaseModel.initially(t => t === make[Tables](make[CrmStore](Nil: Term[List[CrmRecord]], Nil: Term[List[Share]],
    Nil: Term[List[Expiry]]), Nil: Term[List[Event]])))

// ============================================================================
// The database's Scala: SQLite (`Db`), tested against the model; its own store in memory, a variant
// ============================================================================

/** The database's operations on SQLite, each in `IO`: what `databaseModel`'s operations run as. */
final class SqliteDatabase(val db: Db):
  def load: IO[CrmStore] = IO.blocking(db.load())
  def storeAbout(id: BigInt, t: CrmStore): IO[Unit] = IO.blocking { val _ = db.storeAbout(id, t) }
  def logEvent(e: Event): IO[Unit] = IO.blocking(db.logEvent(e))
  def tables: IO[Tables] = IO.blocking(db.tables)

object SqliteDatabase:
  def holding(t: Tables): IO[SqliteDatabase] = IO.blocking(SqliteDatabase(Db.holding(t)))
