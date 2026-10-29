package crm

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
