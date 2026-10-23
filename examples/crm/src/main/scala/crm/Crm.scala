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
val sharedWith = Param[(Record.T, Company.T) => Boolean]("sharedWith",
  "whether the record's company has shared it with the company, and that share holds now")
val asksFor    = Param[(Query.T, Record.T) => Boolean]("asksFor", "whether the record is one the search asks for")
val finds      = Param[(User.T, Query.T, Record.T) => Boolean]("finds", "whether the user's search, run now, returns the record")
val added      = Param[(Company.T, Record.T) => Boolean]("added", "whether a user of the company has added the record to the CRM, for that company")

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

/** A share as a user asked it: of the record with that id, with a company, until a time or for good. */
final case class Grant(record: BigInt, to: TenantId, until: Option[BigInt])

/** What users have asked of the CRM, as far as their companies may ask it: the records added, and the
  * shares given and not since unshared or ended.
  */
final case class Asked(records: List[CrmRecord], grants: List[Grant])

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

/** What a write asks, as far as its author's company may ask it: an Add of a record of their company
  * with a fresh id stores it; a share of a record of their company is made, until the time given (its
  * only time) or for good (with no time); an unshare removes it.
  */
val takesEffect = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  w.change match
    case Change.Add(r) => (r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id)) ==> t.records.contains(r)
    case Change.ShareWith(id, to, until) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==>
      (t.shares.contains(Share(id, to)) && (until match
        case Some(u) => t.expiries.contains(Expiry(id, to, u)) && t.expiries.forall(e => (e.record == id && e.to == to) ==> (e.until == u))
        case None    => !t.expiries.exists(e => e.record == id && e.to == to)))
    case Change.Unshare(id, to) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==> !t.shares.contains(Share(id, to))
}

/** Whether a write adds the record: it asks to add it, of its author's company, under an id no record
  * the store holds has.
  */
val addsRecord = define { (s: CrmStore, w: WriteCmd, r: CrmRecord) =>
  w.change match
    case Change.Add(x) => x == r && r.tenant == w.by.tenant && !s.records.exists(y => y.id == r.id)
    case Change.ShareWith(_, _, _) => false
    case Change.Unshare(_, _) => false
}

/** Whether a write changes the share of the record with that id with the company: it shares or unshares
  * it, and the store holds a record of that id of its author's company.
  */
val changesShare = define { (s: CrmStore, w: WriteCmd, id: BigInt, c: TenantId) =>
  w.change match
    case Change.Add(_) => false
    case Change.ShareWith(i, to, _) => i == id && to == c && s.records.exists(x => x.id == id && x.tenant == w.by.tenant)
    case Change.Unshare(i, to) => i == id && to == c && s.records.exists(x => x.id == id && x.tenant == w.by.tenant)
}

/** A write changes nothing it did not ask: every record the second store holds was held or is the one
  * the write adds, and every share and expiry is held in both stores or is of the share the write changes.
  */
val onlyAsked = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  t.records.forall(r => s.records.contains(r) || addsRecord(s, w, r)) &&
  t.shares.forall(sh => s.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) &&
  s.shares.forall(sh => t.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) &&
  t.expiries.forall(e => s.expiries.contains(e) || changesShare(s, w, e.record, e.to)) &&
  s.expiries.forall(e => t.expiries.contains(e) || changesShare(s, w, e.record, e.to))
}

/** Whether a share has ended by `now`, by the store's expiries. */
val ended = define { (sh: Share, s: CrmStore, now: BigInt) => s.expiries.exists(e => e.record == sh.record && e.to == sh.to && e.until <= now) }

/** The second store is the first with exactly the shares ended by `now` removed, with their times, and
  * the same records.
  */
val endsDueAt = define { (s: CrmStore, now: BigInt, t: CrmStore) =>
  t.records == s.records && t.shares == s.shares.filter(sh => !ended(sh, s, now)) &&
  t.expiries == s.expiries.filter(e => !ended(Share(e.record, e.to), s, now))
}

/** One event: a write, saved by the write side, or a run of the expiry job. */
val stepOf = define { (s: CrmStore, e: Event) =>
  e match
    case Event.Wrote(w)     => afterSave(s, w)
    case Event.Expired(now) => expire(s, now)
}

/** The store a history of events leads to, from the empty store the CRM starts with. */
val runOf = define { (es: List[Event]) => es.foldLeft(CrmStore(Nil, Nil, Nil))((s, e) => stepOf(s, e)) }


// ============================================================================
// What users asked: the history of adds, shares and unshares, with their times
// ============================================================================

/** One more event, as users asked it: an add of a record of its author's company under an id no record
  * added before had; a share or unshare, by a user of the company of the record with that id, which
  * replaces or ends that record's share with that company; a run of the expiry job, which ends the
  * shares whose time it has reached.
  */
val askedStep = define { (a: Asked, e: Event) =>
  e match
    case Event.Wrote(w) =>
      w.change match
        case Change.Add(r) =>
          if r.tenant == w.by.tenant && !a.records.exists(x => x.id == r.id) then Asked(a.records ++ List(r), a.grants) else a
        case Change.ShareWith(id, to, until) =>
          if a.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
            Asked(a.records, a.grants.filter(g => !(g.record == id && g.to == to)) ++ List(Grant(id, to, until)))
          else a
        case Change.Unshare(id, to) =>
          if a.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
            Asked(a.records, a.grants.filter(g => !(g.record == id && g.to == to)))
          else a
    case Event.Expired(now) => Asked(a.records, a.grants.filter(g => g.until.forall(t => now < t)))
}

/** What a history asked, from nothing asked, each event in turn. */
val askedIn = define { (es: List[Event]) => es.foldLeft(Asked(Nil, Nil))((a, e) => askedStep(a, e)) }

/** Whether, after a history, the record with that id is shared with the company at `now`: the last share
  * of it with that company still stands, and its time, if it has one, comes after `now`.
  */
val sharedIn = define { (es: List[Event], id: BigInt, c: TenantId, now: BigInt) =>
  askedIn(es).grants.exists(g => g.record == id && g.to == c && g.until.forall(t => now < t))
}

// ============================================================================
// The root: what a user's search finds, of what users asked
// ============================================================================

val sharedCrm = Node.claim("SharedCrm",
  "A user's search finds a record exactly when it asks for that record, a user of the record's company added it, and it is of the user's company or currently shared with it by its own.",
  why = "The idea in one sentence, stated as exactly over what users asked: what a search finds is fixed by the history of adds, shares and unshares, with their times (Adding, Sharing), whatever the CRM keeps. Both halves matter: a search must never show a record of another company that did not share it, and must show every record a user added that the searcher may see, so a CRM that stores nothing does not meet it. It splits into what the CRM holds (StoreMirrorsRequests) and what searches read of it (Visibility)."
)(forall((u: User.T, q: Query.T) => forall((r: Record.T) =>
    finds(u, q, r) == (asksFor(q, r) && added(owner(r), r) && (owner(r) == companyOf(u) || sharedWith(r, companyOf(u)))))))
  .expects("When Ann at Acme has added a contact, and Gil at Globex a deal he shared with Acme until 100: at 50 Ann finds both, at 150 only her contact, and Gil never finds Ann's contact")(
    (history.value == List(
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.Add(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.ShareWith(2, TenantId("acme"), Some(100)))))) ==>
    (((clock.value == BigInt(50)) ==>
        (results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")) &&
         results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")))) &&
     ((clock.value == BigInt(150)) ==>
        (results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")) &&
         !results(Account("ann@acme", TenantId("acme")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")))) &&
     !results(Account("gil@globex", TenantId("globex")), Ask(Screen.Records, Search.Everything)).contains(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))))
  .expects("A record a user adds to their company, under an id no record added before has, is found from then on by each of their searches that asks for it")(
    forall((u: Account, r: CrmRecord) => forall((pre: List[Event], post: List[Event]) =>
      (history.value == pre ++ (Event.Wrote(WriteCmd(u, Change.Add(r))) :: post) && r.tenant == u.tenant && !askedIn(pre).records.exists(x => x.id == r.id)) ==>
        forall((q: Ask) => askMatches(q, r) ==> results(u, q).contains(r)))))
  .expects("Nothing a user writes changes what anyone finds of another company's records: after the write, a search finds of them what the history before it entitled it to")(
    forall((es: List[Event], w: WriteCmd) => forall((u: Account, q: Ask) => forall((r: CrmRecord) =>
      (history.value == es ++ List(Event.Wrote(w)) && r.tenant != w.by.tenant) ==>
        (results(u, q).contains(r) == (askMatches(q, r) && askedIn(es).records.contains(r) && (r.tenant == u.tenant || sharedIn(es, r.id, u.tenant, clock.value))))))))

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

val adding = Node.definition("Adding",
  "A user of a company has added a record when a write of theirs in the CRM's history asked to add it, of their company, under an id no record added before it had.",
  why = "What the idea calls adding a record, said of the history of requests alone, whatever the CRM keeps: the CRM's records are proven to follow it (StoreMirrorsRequests). A record of another company, or one with an id already taken, is not added: a share names a record by its id, so no two records have one."
)(added := ((c: TenantId, r: CrmRecord) => r.tenant == c && askedIn(history.value).records.contains(r)))

val sharing = Node.definition("Sharing",
  "A record is shared with a company now when the last share or unshare of it with that company, by a user of its company once it was added, was a share, and neither the clock now nor a run of the expiry job since has reached that share's time.",
  why = "What sharing, unsharing and a share's time mean, said of the history alone: the shares the CRM holds are proven to follow it (StoreMirrorsRequests). A share given until a time ends then, whether or not the job has run. A run of the job is in the history with its time: a share it ended stays ended, even before a clock set back."
)(sharedWith := ((r: CrmRecord, c: TenantId) => sharedIn(history.value, r.id, c, clock.value)))

val crmRun = Node.definition("CrmRun",
  "What the CRM holds now, its records, their shares and the shares' expiries, is what its history led to: from empty, each write saved by the write side, the rows about its record replaced by those it stored, and each run of the expiry job, in turn.",
  why = "Nothing else changes the CRM: users write through the write side, and the job ends shares, one at a time, each on what the last left (WriteSideWiring, ExpiryJobWiring); the database replaces the rows about the written record and nothing else (StoreEdits). So the store searches read is the one writes made, and it follows what users asked (StoreMirrorsRequests). The running read side reads these tables from the database, and the event log is this history (ReadSideWiring)."
)(store := runOf(history.value).records, shares := runOf(history.value).shares, expiries := runOf(history.value).expiries)
