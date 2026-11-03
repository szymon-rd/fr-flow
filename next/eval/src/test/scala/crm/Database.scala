package crm

import cats.effect.IO
import frflow.*

// ============================================================================
// The database, as proven code sees it: its operations, Definitions, and their model
// ============================================================================

/** The records, shares and expiries the database holds. */
val load = Definition[Flow[CrmStore]]("the records, shares and expiries the database holds")
/** Holds what a store holds about a record in place of what the database held about it. */
val storeAbout = Definition[(BigInt, CrmStore) => Flow[Unit]](
  "what a store holds about a record, held in place of what the database held about it")
/** Appends an event to the event log. */
val logEvent = Definition[Event => Flow[Unit]]("an event appended to the event log")
/** The database's search: known only by what is assumed of it (G2). */
val fetch = Definition[(Account, Search) => Flow[List[CrmRecord]]](
  "the database's answer to a search: the stored records, of every company, that match it")

/** What the database holds: the store, and the event log. */
final case class Tables(store: CrmStore, events: List[Event]) derives LeanType

/** The database as the proofs see it. */
object databaseModel
    extends StateModel[Tables]("the SQLite database the CRM keeps its records, shares, expiries and event log in"):
  load.means(state.get.map(t => t.store))
  storeAbout.means((id, s) => state.update(t => make[Tables](replaceAbout(t.store, id, aboutRecord(s, id)), t.events)))
  logEvent.means(e => state.update(t => make[Tables](t.store, t.events :+ e)))
  fetch.assumed

/** What the CRM holds now, its history and the time now: the database's and the clock's, the World's (owner §45 D). */
val held: Term[CrmStore] = databaseModel.current.store
val history: Term[List[Event]] = databaseModel.current.events
val clock: Term[BigInt] = Clock.clockModel.current

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

val clockOneAtATime = Node.assumption("A search reads the time once, between two runs on the clock.")(
  Clock.clockModel.atomic)

// ============================================================================
// The database's search: known only by what is assumed of it (G2)
// ============================================================================

val recordsByQuery = Node.assumption("The database returns exactly the stored records that match a search, of " +
    "every company.")(
  forall((user: Term[Account], query: Term[Search]) =>
    fetch(user, query).result.forall(r => held.records.contains(r) && matches(query, r)) &&
      held.records.forall(r => matches(query, r) implies fetch(user, query).result.contains(r))))

val searchKeeps = Node.assumption("A search changes nothing the database holds.")(
  forall((user: Term[Account], query: Term[Search]) =>
    databaseModel.in(fetch(user, query).after) === databaseModel.current))

// ============================================================================
// The database's Scala: SQLite (`Db`), tested against the model; its own store in memory, a variant
// ============================================================================

/** The database's operations on SQLite, each in `IO`: what `databaseModel`'s operations run as. */
final class SqliteDatabase(val db: Db):
  def load: IO[CrmStore] = IO.blocking(db.load())
  def storeAbout(id: BigInt, t: CrmStore): IO[Unit] = IO.blocking { val _ = db.storeAbout(id, t) }
  def logEvent(e: Event): IO[Unit] = IO.blocking(db.logEvent(e))
  def fetch(@annotation.unused user: Account, query: Search): IO[List[CrmRecord]] =
    IO.blocking(db.recordsMatching(query))
  def tables: IO[Tables] = IO.blocking(db.tables)

object SqliteDatabase:
  def holding(t: Tables): IO[SqliteDatabase] = searching(Db.selecting)(t)

  /** A database holding the tables, its searches by the SQL `select` gives (a seeded bug's). */
  def searching(select: Search => (String, List[Any]))(t: Tables): IO[SqliteDatabase] =
    IO.blocking(SqliteDatabase(Db.holding(t, select)))
