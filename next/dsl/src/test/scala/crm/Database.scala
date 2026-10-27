package crm

import frflow.*

// ============================================================================
// The database, as proven code sees it: a boundary, and the model it is decided to behave as
// ============================================================================

/** What proven code may ask of the database. */
trait Database[F[_], T[_]] derives BoundaryOps:
  /** The records, shares and expiries it holds. */
  def load: F[T[CrmStore]]
  /** Holds what `t` holds about the record `id` in place of what it held about it. */
  def storeAbout(id: T[BigInt], t: T[CrmStore]): F[Unit]
  /** Appends an event to the event log. */
  def logEvent(e: T[Event]): F[Unit]

val db = Boundary[Database]("the SQLite database the CRM keeps its records, shares, expiries and event log in")

/** What the database holds: the store, and the event log. */
final case class Tables(store: CrmStore, events: List[Event]) derives LeanType

/** The database as the proofs see it. */
final class StoredTables[F[_]: Flow](state: Model[F, Tables]) extends Database[F, Term]:
  def load: F[Term[CrmStore]] = state.get.map(t => t.store)
  def storeAbout(id: Term[BigInt], s: Term[CrmStore]): F[Unit] = state.get.flatMap(t =>
    state.set(make[Tables](replaceAbout(t.store, id, aboutRecord(s, id)), t.events)))
  def logEvent(e: Term[Event]): F[Unit] = state.get.flatMap(t => state.set(make[Tables](t.store, t.events :+ e)))

val databaseModel = db.model("the store and the event log the database holds")(StoredTables(_))

val tablesModel = Node.assumption("The database holds a store and an event log: it gives the store as it holds it, " +
    "holds the rows a store has about a record in place of those it held about it, leaving the other records' rows, " +
    "and appends an event to the log.")(
  db.behavesAs(databaseModel))

/** The database's answers in memory, the plain Scala `fetch` and `storeRows` are tested with until the SQLite adapter
  * is ported.
  */
object InMemory:
  def recordsMatching(store: CrmStore, q: Search): List[CrmRecord] = store.records.filter(r => q match
    case Search.ById(id)   => r.id == id
    case Search.OfKind(k)  => r.kind == k
    case Search.Everything => true)

  def storeAbout(id: BigInt, t: CrmStore): CrmStore =
    CrmStore(t.records.filter(_.id == id), t.shares.filter(_.record == id), t.expiries.filter(_.record == id))
