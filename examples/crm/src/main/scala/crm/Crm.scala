package crm

import frflow.*

// ============================================================================
// The purpose, in the most general terms
// ============================================================================

val User    = Opaque("User", "a person who works for one of the companies that use the CRM")
val Company = Opaque("Company", "a company that uses the CRM")
val Record  = Opaque("Record", "a contact or a deal kept in the CRM")
val Query   = Opaque("Query", "a search a user runs")

val companyOf  = Param[User.T => Company.T]("companyOf", "the company a user works for")
val owner      = Param[Record.T => Company.T]("owner", "the company a record belongs to")
val stored     = Param[Record.T => Boolean]("stored", "whether the CRM holds the record now")
val sharedWith = Param[(Record.T, Company.T) => Boolean]("sharedWith", "whether the record is shared with the company now")
val asksFor    = Param[(Query.T, Record.T) => Boolean]("asksFor", "whether the record is one the search asks for")
val finds      = Param[(User.T, Query.T, Record.T) => Boolean]("finds", "whether the user's search, run now, returns the record")
val added      = Param[(User.T, Record.T) => Boolean]("added", "whether the user has added the record to the CRM")

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

// What the CRM holds now, its history, the clock, and the database
val history  = Param[List[Event]]("history",
  "the CRM's history since it started empty: every write the write side saved and every run of the expiry job, in order (its event log)")
val store    = Param[List[CrmRecord]]("store", "the records the CRM holds now")
val shares   = Param[List[Share]]("shares", "the shares the CRM holds now")
val expiries = Param[List[Expiry]]("expiries", "the times until which the CRM's shares are given, as it holds them now")
val clock    = Param[BigInt]("clock", "the time now, in seconds, by the server's clock: when a search runs")
val database = Param[Db]("database", "the SQLite database the CRM keeps its records, shares, expiries and event log in")

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

/** Whether the CRM holds a share of the record with that id with the company now, and the share's time,
  * if it was given until one, has not come by the clock.
  */
val sharedNow = define { (id: BigInt, c: TenantId) =>
  shares.value.contains(Share(id, c)) && !expiries.value.exists(e => e.record == id && e.to == c && e.until <= clock.value)
}

/** Whether a reader may see a record: it is their company's, or shared with it now. */
val mayRead = define { (reader: Account, r: CrmRecord) => r.tenant == reader.tenant || sharedNow(r.id, reader.tenant) }

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

/** Whether a history holds a write of the user's adding the record, of their company, under an id no
  * record the CRM held before it had.
  */
val addedIn = define { (es: List[Event], u: Account, r: CrmRecord) =>
  r.tenant == u.tenant && exists((pre: List[Event], post: List[Event]) =>
    es == pre ++ (Event.Wrote(WriteCmd(u, Change.Add(r))) :: post) && !runOf(pre).records.exists(x => x.id == r.id))
}

// ============================================================================
// The root: what users find, add, share and unshare, and what never happens
// ============================================================================

val sharedCrm = Node.claim("SharedCrm",
  "Each user finds by search exactly the stored records of their company and those currently shared with it, and can add their company's records and share or unshare them; a share given until a time ends then, and nothing a user does changes another company's records.",
  why = "The idea in one sentence, stated as exactly: what users can do (find, add, share, unshare) and what must never happen (seeing, or changing, another company's records), so a system that does nothing does not meet it. Finding is said in general terms, fixed by the definitions below, of what the CRM holds now, which is what its history of writes and job runs led to (CrmRun): so a record a user adds is then found. Writing is said in the domain's own terms, of a history and the write after it. A share is current until its time (LiveShares), so a share given until a time ends then, whatever the job has done."
)(forall((u: User.T, q: Query.T) => forall((r: Record.T) =>
    finds(u, q, r) == (stored(r) && asksFor(q, r) && (owner(r) == companyOf(u) || sharedWith(r, companyOf(u)))))) &&
  forall((u: User.T, r: Record.T) => added(u, r) ==> forall((q: Query.T) => asksFor(q, r) ==> finds(u, q, r))) &&
  forall((es: List[Event], w: WriteCmd) => takesEffect(runOf(es), w, runOf(es ++ List(Event.Wrote(w))))) &&
  forall((es: List[Event], w: WriteCmd) => forall((c: TenantId) =>
    (c != w.by.tenant) ==> holdsAlike(runOf(es), runOf(es ++ List(Event.Wrote(w))), c))))
  .expects("When the CRM holds Acme's contact, and Globex's deal shared with Acme until 100: at 50 Ann at Acme finds both, at 150 only her contact, and Gil at Globex never finds Ann's contact")(
    (runOf(history.value) == CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")),
      List(Share(2, TenantId("acme"))), List(Expiry(2, TenantId("acme"), 100)))) ==>
    (((clock.value == BigInt(50)) ==>
        (results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")) &&
         results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")))) &&
     ((clock.value == BigInt(150)) ==>
        (results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")) &&
         !results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")))) &&
     !results(Account("gil@globex", TenantId("globex")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))))
  .expects("When Ann's adding her contact is all the CRM's history, her search for contacts finds it")(
    (history.value == List(Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")))))) ==>
      results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.OfKind(Kind.Contact))).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")))

/** What links writing to finding: one store, so what a user adds is what their searches then find. */
val addedAreFound = Node.claim("AddedAreFound",
  "A record a user adds to their company, under an id no record has, is found from then on by each of their searches that asks for it.",
  why = "What the idea means by users adding records: the write is stored (WritesTakeEffect), nothing later removes it (RecordsKept), and searches read what the CRM holds now (Visibility, CrmRun), so the record is found whatever the CRM does after the write.",
  idea = "Writing records"
)(forall((u: Account, r: CrmRecord) => addedIn(history.value, u, r) ==> forall((q: Ask) => askMatches(q, r) ==> results(u, q).contains(r))))
  .under(sharedCrm)

// ============================================================================
// Definitions: the domain, introduced step by step
// ============================================================================

val companies = Node.definition("Companies",
  "Companies are named by ids; a user is an account of one company; a record, a contact or a deal, belongs to the company stored on it.",
  why = "The CRM knows a company by its id, a user by their account, and stores each record with its company. That the account a request comes with is the caller's own is authentication, not modelled."
)(Company := of[TenantId], User := of[Account], Record := of[CrmRecord],
  companyOf := ((a: Account) => a.tenant), owner := ((r: CrmRecord) => r.tenant))

val searches = Node.definition("Searches",
  "A user searches by id, by kind or for everything, on the records screen or on the sales screen, which asks for deals only, and finds what the search returns.",
  why = "The idea's two ways of finding records: the records screen, and the sales team's screen of deals. What a user finds is what the screen returns, so the screens' code is what the purpose is about."
)(Query := of[Ask], asksFor := ((q: Ask, r: CrmRecord) => askMatches(q, r)), finds := ((u: Account, q: Ask, r: CrmRecord) => results(u, q).contains(r)))

val crmRun = Node.definition("CrmRun",
  "What the CRM holds now, its records, their shares and the shares' expiries, is what its history led to: from empty, each write saved by the write side, the rows about its record replaced by those it stored, and each run of the expiry job, in turn.",
  why = "Nothing else changes the CRM: users write through the write side, and the job ends shares, one at a time, each on what the last left (WriteSideWiring, ExpiryJobWiring); the database replaces the rows about the written record and nothing else (StoreEdits). So the store searches read is the one writes made, and a record a user adds is then found (AddedAreFound). The running read side reads these tables from the database, and the event log is this history (ReadSideWiring)."
)(stored := ((r: CrmRecord) => runOf(history.value).records.contains(r)),
  store := runOf(history.value).records, shares := runOf(history.value).shares, expiries := runOf(history.value).expiries)

val liveShares = Node.definition("LiveShares",
  "A record is shared with a company now when the CRM holds a share of its id with that company, and the share's time, if it was given until one, has not come.",
  why = "A share given until a time ends at that time, whatever the expiry job has done: a search compares the share's expiry with the clock, so a share never outlives its time, and the job only clears rows that have ended. A share names a record by its id (StoreConsistent keeps ids unique)."
)(sharedWith := ((r: CrmRecord, c: TenantId) => sharedNow(r.id, c)))

val adding = Node.definition("Adding",
  "A user has added a record when a write of theirs in the CRM's history asked to add it, of their company, under an id no record the CRM held then had.",
  why = "What the idea calls adding a record: the write side refuses a record of another company or one with a taken id, and such a write adds nothing."
)(added := ((u: Account, r: CrmRecord) => addedIn(history.value, u, r)))
