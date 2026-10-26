package crm

import frflow.*

// ============================================================================
// The database, as proven code sees it: a boundary, and the model it is decided to behave as
// ============================================================================

/** What proven code may ask of the database. */
trait Database:
  /** The records, shares and expiries it holds. */
  def load: Flow[CrmStore]
  /** Holds what `t` holds about the record `id` in place of what it held about it. */
  def storeAbout(id: Term[BigInt], t: Term[CrmStore]): Flow[Unit]
  /** Appends an event to the event log. */
  def logEvent(e: Term[Event]): Flow[Unit]

val db = Boundary[Database]("database", "the SQLite database the CRM keeps its records, shares, expiries and event log in")

/** What the database holds: the store, and the event log. */
final case class Tables(store: CrmStore, events: List[Event])
object Tables extends Data[Tables]

/** The database as the proofs see it. */
object DatabaseModel extends Database, StateModel[Tables]:
  def load = state.get.map(t => t.store)
  def storeAbout(id: Term[BigInt], s: Term[CrmStore]) = state.update(t => Tables(replaceAbout(t.store, id, aboutRecord(s, id)), t.events))
  def logEvent(e: Term[Event]) = state.update(t => Tables(t.store, t.events ++ List(e)))

val tablesModel = Node.assumption(db)(DatabaseModel)("The database holds a store and an event log: it gives the store as it holds it, holds the rows a store has about a record in place of those it held about it, leaving the other records' rows, and appends an event to the log.",
  why = "Records, shares, expiries and the event log live in SQLite. Proven flows are proven from this model, not from the SQL; the SQLite adapter (SqliteDatabase) does this by deleting and inserting the record's rows in one transaction, and by inserting into the events table. MemoryDatabase, the CRM's own in-memory store for development and tests, is tested against this model; SQLite, an outside system, is checked against it.",
  idea = "Expiring shares")
  .checkedAgainst(t => SqliteDatabase.holding(t), _.tables)
  .implementedBy(t => MemoryDatabase.holding(t), _.tables)

/** The database in production: SQLite, through the adapter in Db.scala, DbWrites.scala and EventLog.scala. */
final class SqliteDatabase(sql: Db) extends Database:
  /** What it holds, read back. */
  def tables: Tables = Tables(sql.load(), sql.events())
  def load = Flow.effect(sql.load())
  def storeAbout(id: Term[BigInt], t: Term[CrmStore]) = Flow.effect(id, t)((i, s) => { sql.storeAbout(i, s); () })
  def logEvent(e: Term[Event]) = Flow.effect(e)(sql.logEvent)

object SqliteDatabase:
  /** An in-memory database holding the given tables: for examples and tests. */
  def holding(t: Tables): SqliteDatabase =
    val d = Db.of(t.store.records, t.store.shares, t.store.expiries)
    t.events.foreach(d.logEvent)
    SqliteDatabase(d)
