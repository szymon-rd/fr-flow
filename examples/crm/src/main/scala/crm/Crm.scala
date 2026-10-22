package crm

import frflow.*

// ============================================================================
// The purpose, in the most general terms
// ============================================================================

val User    = Opaque("User", "a person who works for one of the companies that use the CRM")
val Company = Opaque("Company", "a company that uses the CRM")
val Record  = Opaque("Record", "a contact or a deal kept in the CRM")
val Query   = Opaque("Query", "a search a user runs")
val Store   = Opaque("Store", "what the CRM holds at a moment")
val Write   = Opaque("Write", "a change a user asks of the CRM")
val Time    = Opaque("Time", "a moment, as the expiry job reads the clock")

val companyOf  = Param[User.T => Company.T]("companyOf", "the company a user works for")
val owner      = Param[Record.T => Company.T]("owner", "the company a record belongs to")
val stored     = Param[Record.T => Boolean]("stored", "whether the record is stored when the search runs")
val sharedWith = Param[(Record.T, Company.T) => Boolean]("sharedWith", "whether the record is shared with the company when the search runs")
val asksFor    = Param[(Query.T, Record.T) => Boolean]("asksFor", "whether the record is one the search asks for")
val finds      = Param[(User.T, Query.T, Record.T) => Boolean]("finds", "whether the user's search returns the record")
val author     = Param[Write.T => User.T]("author", "the user who asks for the write")
val storeAfter = Param[(Store.T, Write.T) => Store.T]("storeAfter", "what the CRM holds after a write, when it held the given store")
val obeys      = Param[(Store.T, Write.T, Store.T) => Boolean]("obeys",
  "whether the second store holds what the write asked of the first, as far as its author's company may ask it")
val alike      = Param[(Store.T, Store.T, Company.T) => Boolean]("alike",
  "whether two stores hold the company's records alike: the same records, shared with the same companies until the same times")
val reached    = Param[Store.T => Boolean]("reached", "whether the CRM can come to hold the store, from its start, by users' writes and runs of the expiry job")
val expiryRun  = Param[(Store.T, Time.T) => Store.T]("expiryRun", "what the CRM holds after the expiry job runs at the time, when it held the given store")
val endsDue    = Param[(Store.T, Time.T, Store.T) => Boolean]("endsDue",
  "whether the second store is the first with exactly the shares given until the time, or earlier, ended")

val sharedCrm = Node.claim("SharedCrm",
  "Each user finds by search exactly the stored records of their company and those currently shared with it, and can add their company's records and share or unshare them; a share given until a time ends then, and nothing a user does changes another company's records.",
  why = "The idea in one sentence, stated as exactly: what users can do (find, add, share, unshare) and what must never happen (seeing, or changing, another company's records), so a system that does nothing does not meet it. Companies, users, records, storing, sharing and searching are left open here; the definitions below fix them."
)(forall((u: User.T, q: Query.T) => forall((r: Record.T) =>
    finds(u, q, r) == (stored(r) && asksFor(q, r) && (owner(r) == companyOf(u) || sharedWith(r, companyOf(u)))))) &&
  forall((s: Store.T, w: Write.T) => obeys(s, w, storeAfter(s, w))) &&
  forall((s: Store.T, t: Time.T) => endsDue(s, t, expiryRun(s, t))) &&
  forall((s: Store.T, w: Write.T) => reached(s) ==> forall((c: Company.T) => (c != companyOf(author(w))) ==> alike(s, storeAfter(s, w), c))))

// ============================================================================
// The domain: companies, records, shares, searches, writes, the expiry job
// ============================================================================

final case class TenantId(value: String)
final case class Account(email: String, tenant: TenantId)

enum Kind:
  case Contact, Deal

final case class CrmRecord(id: BigInt, tenant: TenantId, kind: Kind, title: String)
final case class Share(record: BigInt, to: TenantId)

/** Until when a share holds (a time in seconds); a share with none holds until it is unshared. */
final case class Expiry(record: BigInt, to: TenantId, until: BigInt)

enum Search:
  case ById(id: BigInt)
  case OfKind(kind: Kind)
  case Everything

enum Screen:
  case Records, Sales

/** A search, on a screen: the records screen, or the sales screen (deals only). */
final case class Ask(screen: Screen, search: Search)

final case class CrmStore(records: List[CrmRecord], shares: List[Share], expiries: List[Expiry])

enum Change:
  case Add(record: CrmRecord)
  case ShareWith(record: BigInt, to: TenantId, until: Option[BigInt])
  case Unshare(record: BigInt, to: TenantId)

final case class WriteCmd(by: Account, change: Change)

/** What changes the store: a user's write, or a run of the expiry job at a time. */
enum Event:
  case Wrote(cmd: WriteCmd)
  case Expired(now: BigInt)

// The data, as stored when a search runs, and the database
val store    = Param[List[CrmRecord]]("store", "the record table as stored when the search runs")
val shares   = Param[List[Share]]("shares", "the share table as stored when the search runs")
val database = Param[Db]("database", "the SQLite database the CRM keeps its records, shares and expiries in")

// The operations: what the system does, each implemented by code
val read      = Param[(Account, Search) => List[CrmRecord]]("read", "the records screen: the records a user's search returns")
val deals     = Param[(Account, Search) => List[CrmRecord]]("deals", "the sales screen: the deals a user's search returns")
val fetch     = Param[(Account, Search) => List[CrmRecord]]("fetch", "the database's answer to a search: the stored records, of every company, that match it")
val write     = Param[(CrmStore, WriteCmd) => CrmStore]("write", "a write applied to a store: the store it leads to")
val save      = Param[(CrmStore, WriteCmd) => CrmStore]("save",
  "the write side: a write applied to the store the database holds, the rows about its record stored; it returns those rows as read back")
val storeRows = Param[(BigInt, CrmStore) => CrmStore]("storeRows",
  "the database storing what a store holds about one record in place of what it held about it; it returns the rows about the record, read back")
val expire    = Param[(CrmStore, BigInt) => CrmStore]("expire", "a run of the expiry job at a time (in seconds) on a store: the store it leads to")

/** Whether a record is one a search asks for. */
val matches = define { (q: Search, r: CrmRecord) =>
  q match
    case Search.ById(id)   => r.id == id
    case Search.OfKind(k)  => r.kind == k
    case Search.Everything => true
}

/** Whether a reader may see a record: it is their company's, or shared with it. */
val mayRead = define { (reader: Account, r: CrmRecord) => r.tenant == reader.tenant || shares.value.contains(Share(r.id, reader.tenant)) }

/** Whether a record is one a search on a screen asks for: the sales screen asks for deals only. */
val askMatches = define { (q: Ask, r: CrmRecord) =>
  q.screen match
    case Screen.Records => matches(q.search, r)
    case Screen.Sales   => r.kind == Kind.Deal && matches(q.search, r)
}

/** What a search on a screen returns: the records screen's, or the sales screen's. */
val results = define { (u: Account, q: Ask) =>
  q.screen match
    case Screen.Records => read(u, q.search)
    case Screen.Sales   => deals(u, q.search)
}

/** The record a write is about. */
val about = define { (w: WriteCmd) =>
  w.change match
    case Change.Add(r) => r.id
    case Change.ShareWith(id, _, _) => id
    case Change.Unshare(id, _) => id
}

/** What a store holds about one record: the record (by its id), its shares and their expiries. */
val aboutRecord = define { (s: CrmStore, id: BigInt) =>
  CrmStore(s.records.filter(r => r.id == id), s.shares.filter(sh => sh.record == id), s.expiries.filter(e => e.record == id))
}

/** A store with what it holds about one record replaced by the given rows. */
val replaceAbout = define { (s: CrmStore, id: BigInt, rows: CrmStore) =>
  CrmStore(s.records.filter(r => r.id != id) ++ rows.records, s.shares.filter(sh => sh.record != id) ++ rows.shares,
    s.expiries.filter(e => e.record != id) ++ rows.expiries)
}

/** What the database holds after the write side saves a write: what it held, with the rows about the
  * written record replaced by those it stored.
  */
val afterSave = define { (s: CrmStore, w: WriteCmd) => replaceAbout(s, about(w), save(s, w)) }

/** No two records have one id. */
val idsUnique = define { (s: CrmStore) => s.records.forall(a => s.records.forall(b => (a.id == b.id) ==> (a == b))) }

/** What a write asks, as far as its author's company may ask it: an Add of a record of their company
  * with a fresh id stores it; a share of a record of their company is made (until the time given, or
  * for good); an unshare removes it.
  */
val takesEffect = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  w.change match
    case Change.Add(r) => (r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id)) ==> t.records.contains(r)
    case Change.ShareWith(id, to, until) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==>
      (t.shares.contains(Share(id, to)) && (until match
        case Some(u) => t.expiries.contains(Expiry(id, to, u))
        case None    => !t.expiries.exists(e => e.record == id && e.to == to)))
    case Change.Unshare(id, to) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==> !t.shares.contains(Share(id, to))
}

/** Two stores hold the same shares, and expiries, of the record with the given id. */
val rowsAlike = define { (s: CrmStore, t: CrmStore, id: BigInt) =>
  s.shares.forall(sh => (sh.record == id) ==> t.shares.contains(sh)) && t.shares.forall(sh => (sh.record == id) ==> s.shares.contains(sh)) &&
  s.expiries.forall(e => (e.record == id) ==> t.expiries.contains(e)) && t.expiries.forall(e => (e.record == id) ==> s.expiries.contains(e))
}

/** Two stores hold a company's records alike: the same records, with the same shares and expiries. */
val holdsAlike = define { (s: CrmStore, t: CrmStore, c: TenantId) =>
  s.records.forall(r => (r.tenant == c) ==> (t.records.contains(r) && rowsAlike(s, t, r.id))) && t.records.forall(r => (r.tenant == c) ==> s.records.contains(r))
}

/** Whether a share has ended by `now`, by the store's expiries. */
val ended = define { (sh: Share, s: CrmStore, now: BigInt) => s.expiries.exists(e => e.record == sh.record && e.to == sh.to && e.until <= now) }

/** The second store is the first with exactly the shares ended by `now` removed, and the same records. */
val endsDueAt = define { (s: CrmStore, now: BigInt, t: CrmStore) => t.records == s.records && t.shares == s.shares.filter(sh => !ended(sh, s, now)) }

/** One event: a write, saved by the write side, or a run of the expiry job. */
val stepOf = define { (s: CrmStore, e: Event) =>
  e match
    case Event.Wrote(w)     => afterSave(s, w)
    case Event.Expired(now) => expire(s, now)
}

/** The store a history of events leads to, from the empty store the CRM starts with. */
val runOf = define { (es: List[Event]) => es.foldLeft(CrmStore(Nil, Nil, Nil))((s, e) => stepOf(s, e)) }

// ============================================================================
// Definitions: the domain, introduced step by step
// ============================================================================

val companies = Node.definition("Companies",
  "Companies are named by ids; a user is an account of one company; a record, a contact or a deal, belongs to the company stored on it.",
  why = "The CRM knows a company by its id, a user by their account, and stores each record with its company. That the account a request comes with is the caller's own is authentication, not modelled."
)(Company := of[TenantId], User := of[Account], Record := of[CrmRecord],
  companyOf := ((a: Account) => a.tenant), owner := ((r: CrmRecord) => r.tenant))

val recordTable = Node.definition("RecordTable",
  "A record is stored when the record table holds it, as stored when the search runs.",
  why = "Records live in a table of the database; what a search can find is what that table holds when it runs."
)(stored := ((r: CrmRecord) => store.value.contains(r)))

val sharesById = Node.definition("SharesById",
  "A record is shared with a company when the share table holds a share of its id with that company.",
  why = "A share names a record by its id, the way a company refers to its records; so a share shows every record with that id, and ids must be unique across companies (StoreConsistent)."
)(sharedWith := ((r: CrmRecord, c: TenantId) => shares.value.contains(Share(r.id, c))))

val searches = Node.definition("Searches",
  "A user searches by id, by kind or for everything, on the records screen or on the sales screen, which asks for deals only, and finds what the search returns.",
  why = "The idea's two ways of finding records: the records screen, and the sales team's screen of deals. What a user finds is what the screen returns, so the screens' code is what the purpose is about."
)(Query := of[Ask], asksFor := ((q: Ask, r: CrmRecord) => askMatches(q, r)), finds := ((u: Account, q: Ask, r: CrmRecord) => results(u, q).contains(r)))

val stores = Node.definition("Stores",
  "The CRM holds records, shares and share expiries; a write is a user's change: adding a record, sharing one until a time or for good, or unsharing one.",
  why = "The idea's writes: users add records and share or unshare them, a share possibly until a given time. Editing or removing records is not modelled."
)(Store := of[CrmStore], Write := of[WriteCmd], author := ((w: WriteCmd) => w.by))

val saving = Node.definition("Saving",
  "After a write, the CRM holds what it held, with the rows about the written record replaced by those the write side saved.",
  why = "The database holds the store; the write side stores only the rows about the record a write is about, so a write costs the same whatever the size of the store. That nothing else changes the database is trusted (StoreEdits)."
)(storeAfter := ((s: CrmStore, w: WriteCmd) => afterSave(s, w)))

val asked = Node.definition("Asked",
  "A write obeys its author when it stores a new record of their company, makes a share of their company's record (until the time given, or for good), or removes one, as asked.",
  why = "What users can do with their company's records, in the idea's words. A write of another company's record, or of a record with a taken id, may do nothing."
)(obeys := ((s: CrmStore, w: WriteCmd, t: CrmStore) => takesEffect(s, w, t)))

val companyRecords = Node.definition("CompanyRecords",
  "Two stores hold a company's records alike when they hold the same records of it, with the same shares and expiries.",
  why = "A company's records are its records and whom they are shared with until when: changing any of them changes what other users can see of the company."
)(alike := ((s: CrmStore, t: CrmStore, c: TenantId) => holdsAlike(s, t, c)))

val history = Node.definition("History",
  "The CRM starts empty, and reaches a store by writes, each saved by the write side, and runs of the expiry job, one after another.",
  why = "Nothing else changes the store: users write, and the job ends shares. A property kept by every write and every run then holds of every store the CRM reaches."
)(reached := ((s: CrmStore) => exists((es: List[Event]) => runOf(es) == s)))

val expiryRuns = Node.definition("ExpiryRuns",
  "Time is counted in seconds; a run of the expiry job at a time ends exactly the shares given until then or earlier, and keeps the records.",
  why = "A share given until a time must end then; a job that runs every minute ends it, so a share outlives its time by a minute at most. The job touches nothing else."
)(Time := of[BigInt], expiryRun := ((s: CrmStore, now: BigInt) => expire(s, now)),
  endsDue := ((s: CrmStore, now: BigInt, t: CrmStore) => endsDueAt(s, now, t)))
