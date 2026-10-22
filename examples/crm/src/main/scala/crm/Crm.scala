package crm

import frflow.*

// ============================================================================
// Root: tenant isolation, generic
// ============================================================================

val Tenant = Opaque("Tenant", "a company that uses the CRM")
val User   = Opaque("User", "a person who works for a company")
val Record = Opaque("Record", "a contact or a deal kept in the CRM")

val tenantOf   = Param[User.T => Tenant.T]("tenantOf", "the company a user works for")
val owner      = Param[Record.T => Tenant.T]("owner", "the company a record belongs to")
val sharedWith = Param[(Record.T, Tenant.T) => Boolean]("sharedWith", "whether the record's company shared it with the given company")
val stored     = Param[Record.T => Boolean]("stored", "whether the record is kept in the CRM")

/** A user may see a record of their own company, or one shared with it. */
val visible = define { (u: User.T, r: Record.T) => owner(r) == tenantOf(u) || sharedWith(r, tenantOf(u)) }

/** Model: whom the system shows which records. */
val isolation = Node.root[(User.T, Record.T) => Boolean](
  "TenantIsolation",
  "A user sees exactly the stored records of their company and those shared with their company.",
  why = "Isolation between companies is what the idea says must hold, and finding records is what it says users can do: the two together say which records a user sees. Companies, users, records, storing and sharing are left open.",
  idea = "Reading records"
)(shows => forall((u: User.T, r: Record.T) => shows(u, r) == (stored(r) && visible(u, r))))

// ============================================================================
// Users see records only through queries
// ============================================================================

val Query = Opaque("Query", "a search a user runs")
val everything = Param[Query.T]("everything", "the search that lists everything a user can see")

/** Model: what a query returns to a user. */
val readApi = isolation.refine[(User.T, Query.T) => List[Record.T]](
  "ReadApi",
  "Records are shown only as query results; a query returns only stored records the user may see, and listing everything returns all of them.",
  why = "Users find records by searching, so what a user sees is what their queries return. abs: a user is shown a record when some query of theirs returns it."
)(
  abs  = run => (u, r) => exists((q: Query.T) => run(u, q).contains(r)),
  spec = run => forall((u: User.T, q: Query.T) => run(u, q).forall(r => stored(r) && visible(u, r))) &&
    forall((u: User.T, r: Record.T) => (stored(r) && visible(u, r)) ==> run(u, everything.value).contains(r))
)

// ============================================================================
// Instantiation: the concrete CRM domain
// ============================================================================

final case class TenantId(value: String)
final case class Account(email: String, tenant: TenantId)

enum Kind:
  case Contact, Deal

final case class CrmRecord(id: BigInt, tenant: TenantId, kind: Kind, title: String)
final case class Share(record: BigInt, to: TenantId)

enum Search:
  case ById(id: BigInt)
  case OfKind(kind: Kind)
  case Everything

val store = Param[List[CrmRecord]]("store", "the records as stored when the search runs")

val shares = Param[List[Share]]("shares", "the share table as stored when the search runs; a share names a record by its id, which is unique across all companies in every store writes reach (Accounts relies on CrmWrites for it)")

val accounts = readApi.instantiate[(Account, Search) => List[CrmRecord]](
  "Accounts",
  "Users are accounts of a company, records are contacts and deals, and sharing is a table of shares.",
  why = "A record belongs to the company stored on it, and a user to the company of their account. This trusts the record, so ReadContract requires returned records to be the stored ones; it also trusts the account, which authentication provides (not modelled)."
)(
  Tenant     := of[TenantId],
  User       := of[Account],
  Record     := of[CrmRecord],
  Query      := of[Search],
  tenantOf   := ((a: Account) => a.tenant),
  owner      := ((r: CrmRecord) => r.tenant),
  sharedWith := ((r: CrmRecord, t: TenantId) => shares.value.contains(Share(r.id, t))),
  stored     := ((r: CrmRecord) => store.value.contains(r)),
  everything := Search.Everything
).relies(crmWrites, "a share names one record by its id: ids are unique in every store the writes reach, so a share never shows another company's record with the same id",
  (s: CrmStore) => consistentStore(s))(() => CrmStore(store.value, shares.value, Nil))

// ============================================================================
// Contract for implementations
// ============================================================================

/** Whether a record is one a search asks for. */
val matches = define { (q: Search, r: CrmRecord) =>
  q match
    case Search.ById(id)  => r.id == id
    case Search.OfKind(k) => r.kind == k
    case Search.Everything => true
}

/** Whether a reader may see a record: it is their company's, or shared with it. The rule every read keeps. */
val mayRead = define { (reader: Account, r: CrmRecord) => r.tenant == reader.tenant || shares.value.contains(Share(r.id, reader.tenant)) }

/** One rule for every read path, stated once: a reader is shown a record only if their company may see it. */
val noCrossTenantRead = Node.invariant[Account, CrmRecord](
  "NoCrossTenantRead",
  "No read returns a record of another company unless that company shared it with the reader's.",
  why = "The isolation every read path of the CRM must keep, stated once. Every contract keeps it, listing the records a call shows to whom, or says why it shows none; so a new read path (an export, an admin view) cannot leave it out unnoticed."
)((reader, r) => mayRead(reader, r))

// ============================================================================
// Port: the database, outside the proven core
// ============================================================================

val database = Param[Db]("database", "the SQLite database the CRM keeps its records and shares in")

/** What the database is trusted to do: return exactly the stored records a search asks for. */
val recordsByQuery = Node.port[Account, Search, List[CrmRecord]](
  "RecordsByQuery",
  "The database returns exactly the stored records that match a search.",
  why = "Records live in SQLite. The read side is proven from this promise, not from the SQL; the SQL is checked against the define the port is decided with on its examples, and every result it returns is checked to match the search."
)((user, query, rs) => rs.forall(r => store.value.contains(r) && matches(query, r)) && store.value.forall(r => matches(query, r) ==> rs.contains(r)))
  .checkedBy((user, query, rs) => rs.forall(r => matches(query, r)))
  .examples(
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    database.bind(Db.of(store.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "every company's contacts: the database does not filter by company, the read side does"),
    expect(Account("ann@acme", TenantId("acme")), Search.ById(1), List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), "a record by its id"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "a stored record is never left out"))
  .exempt(noCrossTenantRead, "it returns records to the read side's code, never to a reader: ReadContract keeps the rule")

/** The records a search asks for, as the port promises them: what the SQL is checked against. */
val storedMatching = define { (user: Account, query: Search) => store.value.filter(r => matches(query, r)) }

/** In the read side's code: the database, called by its promise. */
val fetch = recordsByQuery.caller("fetch")

val readContract = accounts.contract[Account, Search, List[CrmRecord]](
  "ReadContract",
  "A search returns exactly the stored records that match it and the user may see: each of the user's company or shared with it.",
  why = "Accounts, stated for one call, plus what a search asks for. A returned record must be one of the stored records, so an implementation cannot relabel another company's record as the user's; and every such record is returned, since the idea says users find records."
)((user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .examples(
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    shares.bind(Nil), database.bind(Db.of(store.value, shares.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "Ann lists everything she can see: Acme's deal"),
    expect(Account("ann@acme", TenantId("acme")), Search.ById(2), Nil, "Globex's contact is not shared with Acme"),
    reject(Account("ann@acme", TenantId("acme")), Search.ById(2), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "another company's record is never returned"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(2, TenantId("acme"), Kind.Contact, "Globex contact")),
      "a record relabelled as Acme's is not a stored record"),
    reject(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "a search for contacts does not return deals"))
  .examples(
    store.bind(List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    shares.bind(List(Share(2, TenantId("acme")))), database.bind(Db.of(store.value, shares.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "Globex shared its contact with Acme, so Ann finds it by kind"))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))
  .checkedBy((user, query, result) => result.forall(r => matches(query, r) && mayRead(user, r)))
  .expects("Someone at Acme never sees a Globex record that Globex did not share with Acme, whatever they search for")(run =>
    forall((u: Account, q: Search) => (u.tenant == TenantId("acme")) ==>
      run(u, q).forall(r => (r.tenant == TenantId("globex")) ==> shares.value.contains(Share(r.id, TenantId("acme"))))))

/** The production wiring, owned as a component: changes to it are reviewed. */
val readSideWiring = readContract.design(
  "ReadSideWiring",
  "The read side serves searches through service, which checks every result against ReadContract and the invariants it keeps.",
  why = "Every path to the records must go through service; keeping the wiring in one governed file makes a change to it visible."
)("src/main/scala/crm/ReadSide.scala")
  .exempt(noCrossTenantRead, "it returns no records itself: every read goes through service, which checks each result against ReadContract and the invariant")

// ============================================================================
// Implementation, in the Scala Lean translates: proven to keep ReadContract
// ============================================================================

/** A search: what the database returns for it, of the user's company or shared with it. */
val search = define { (user: Account, query: Search) =>
  fetch(user, query).filter(r => mayRead(user, r))
}

/** Code built on another contract: `rc` stands for any code meeting ReadContract. DealSearch is
  * proven from ReadContract's promise alone; at run time `rc` is ReadContract's service.
  */
val rc = readContract.caller("rc")

/** Model: what the sales screen lists for a user's search. */
val salesScreen = Node.root[(Account, Search) => List[CrmRecord]](
  "SalesScreen",
  "The sales screen lists exactly the stored deals that match a search and the user may see.",
  why = "The idea's sales screen: deals only, and every deal the user may see; what a user may see is the same rule as for reading records.",
  idea = "Sales screen"
)(run => forall((u: Account, q: Search) =>
  run(u, q).forall(r => store.value.contains(r) && r.kind == Kind.Deal && matches(q, r) && mayRead(u, r)) &&
  store.value.forall(r => (r.kind == Kind.Deal && matches(q, r) && mayRead(u, r)) ==> run(u, q).contains(r))))

val dealSearch = salesScreen.contract[Account, Search, List[CrmRecord]](
  "DealSearch",
  "A deal search returns exactly the stored deals that match it and the user may see.",
  why = "SalesScreen, stated for one call. It is built on ReadContract, so it shows only what ReadContract may show."
)((user, query, result) => result.forall(r => store.value.contains(r) && r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .examples(
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact"))),
    shares.bind(Nil), database.bind(Db.of(store.value, shares.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "Ann's deal search lists Acme's deal, not its contact"),
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), Nil, "a search for contacts finds no deal"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact")),
      "a contact is never listed as a deal"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, Nil, "a deal Ann may see is never left out"))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))

/** Deals: what ReadContract returns, keeping only deals. */
val deals = define { (user: Account, query: Search) => rc(user, query).filter(r => r.kind == Kind.Deal) }

// ============================================================================
// Root: writes keep the store consistent, and touch only the author's company
// ============================================================================

val Store = Opaque("Store", "the records and shares as stored")
val Write = Opaque("Write", "a change a user asks for: adding a record, or sharing or unsharing one")

val initial    = Param[Store.T]("initial", "the store the CRM starts with")
val consistent = Param[Store.T => Boolean]("consistent", "whether every share is of a stored record, and no two records have one id")
val permitted  = Param[(Store.T, Write.T, Store.T) => Boolean]("permitted",
  "whether the change from the first store to the second is one the write's author may make: it touches only their company's records and shares")
val effect     = Param[(Store.T, Write.T, Store.T) => Boolean]("effect",
  "whether the second store holds what the write asked for, when its author's company may ask it")

/** Model: the store a sequence of writes leads to, from the initial store. */
val writesKeepStore = Node.root[List[Write.T] => Store.T](
  "WritesKeepStore",
  "Every store the CRM reaches by writes is consistent, every write changes only what its author's company may change, and a write its author's company may make takes effect.",
  why = "The idea's rules for writing, over every sequence of writes from the initial store: consistency of every store reached, authority of each write, and what users can do (add, share, unshare). What consistency, authority and effect mean is left open.",
  idea = "Writing records"
)(run => forall((ws: List[Write.T]) => consistent(run(ws))) &&
  forall((ws: List[Write.T], w: Write.T) => permitted(run(ws), w, run(ws ++ List(w))) && effect(run(ws), w, run(ws ++ List(w)))))

/** Model: one write. */
val stepByStep = writesKeepStore.refine[(Store.T, Write.T) => Store.T](
  "StepByStep",
  "The CRM starts consistent, a write keeps a consistent store consistent, and every write is permitted and takes effect.",
  why = "A store is reached by applying writes one at a time from the initial store, so it is enough that the initial store is consistent and that each write keeps consistency (by induction over the writes) and is permitted. abs: the store after a sequence of writes is the writes applied in turn."
)(
  abs = apply => ws => ws.foldLeft(initial.value)((s, w) => apply(s, w)),
  spec = apply => consistent(initial.value) && forall((s: Store.T, w: Write.T) => (consistent(s) ==> consistent(apply(s, w))) && permitted(s, w, apply(s, w)) && effect(s, w, apply(s, w))))

/** Until when a share holds (a time in seconds); a share with none holds until it is unshared. */
final case class Expiry(record: BigInt, to: TenantId, until: BigInt)

final case class CrmStore(records: List[CrmRecord], shares: List[Share], expiries: List[Expiry])

enum Change:
  case Add(record: CrmRecord)
  case ShareWith(record: BigInt, to: TenantId, until: Option[BigInt])
  case Unshare(record: BigInt, to: TenantId)

final case class WriteCmd(by: Account, change: Change)

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

/** A write changes only what the store holds about its record: every row about another record is kept, and none is added. */
val touchesOnly = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  s.records.forall(r => r.id == about(w) || t.records.contains(r)) && t.records.forall(r => r.id == about(w) || s.records.contains(r)) &&
  s.shares.forall(sh => sh.record == about(w) || t.shares.contains(sh)) && t.shares.forall(sh => sh.record == about(w) || s.shares.contains(sh)) &&
  s.expiries.forall(e => e.record == about(w) || t.expiries.contains(e)) && t.expiries.forall(e => e.record == about(w) || s.expiries.contains(e))
}

/** A consistent store: every share is of a stored record, no two records have one id, and every expiry is of a share. */
val consistentStore = define { (s: CrmStore) =>
  s.shares.forall(sh => s.records.exists(r => r.id == sh.record)) && s.records.forall(a => s.records.forall(b => (a.id == b.id) ==> (a == b))) &&
  s.expiries.forall(e => s.shares.contains(Share(e.record, e.to)))
}

/** What a permitted write does: an Add of a record of the author's company with a fresh id stores it; a
  * share of a record of the author's company is made (until the time given, or with no end); an unshare
  * removes it.
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

/** What a write may change: only its author's company's records, and only shares and expiries of their company's records. */
val permittedWrite = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  t.records.filter(r => r.tenant != w.by.tenant) == s.records.filter(r => r.tenant != w.by.tenant) &&
  t.shares.forall(sh => s.shares.contains(sh) || t.records.exists(r => r.id == sh.record && r.tenant == w.by.tenant)) &&
  s.shares.forall(sh => t.shares.contains(sh) || s.records.exists(r => r.id == sh.record && r.tenant == w.by.tenant)) &&
  t.expiries.forall(e => s.expiries.contains(e) || t.records.exists(r => r.id == e.record && r.tenant == w.by.tenant)) &&
  s.expiries.forall(e => t.expiries.contains(e) || s.records.exists(r => r.id == e.record && r.tenant == w.by.tenant))
}

val crmWrites = stepByStep.instantiate[(CrmStore, WriteCmd) => CrmStore](
  "CrmWrites",
  "The store is the CRM's records, shares and share expiries; a write is a user's change; a store is consistent when every share is of a stored record, record ids are unique and every expiry is of a share; a write may change only its author's company's records, and add or remove only shares and expiries of their company's records.",
  why = "A share names a record by its id: a share of a record that is not stored would show the next record stored with that id, and two records with one id would both be shared by it, across companies; an expiry of no share would end a share made later. Authority is by the author's account, which authentication provides (not modelled). Records of other companies must come out of a write exactly as they went in."
)(
  Store      := of[CrmStore],
  Write      := of[WriteCmd],
  initial    := CrmStore(Nil, Nil, Nil),
  consistent := ((s: CrmStore) => consistentStore(s)),
  permitted  := ((s: CrmStore, w: WriteCmd, t: CrmStore) => permittedWrite(s, w, t)),
  effect     := ((s: CrmStore, w: WriteCmd, t: CrmStore) => takesEffect(s, w, t))
)

val writeContract = crmWrites.contract[CrmStore, WriteCmd, CrmStore](
  "WriteContract",
  "A write keeps the store consistent, changes only the author's company's records and only shares of their company's records, takes effect when its author's company may make it, and changes nothing about other records than its own.",
  why = "CrmWrites, stated for one call, plus what the idea promises a user can do: add records for their company, and share (until a time, or with no end) or unshare them. A write the company may not make changes nothing. That a write touches only its own record is what lets the write side store only that record's rows."
)((s, w, t) => (consistentStore(s) ==> consistentStore(t)) && permittedWrite(s, w, t) && takesEffect(s, w, t) && touchesOnly(s, w, t))
  // Per call, in time linear in the store: the write took effect, and other companies' records are as they were.
  // The rest (consistency, what it touches) is proven of the code, and would read every pair of rows.
  .checkedBy((s, w, t) => takesEffect(s, w, t) && t.records.filter(r => r.tenant != w.by.tenant) == s.records.filter(r => r.tenant != w.by.tenant))
  .examples()(
    expect(CrmStore(Nil, Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil),
      "Ann adds a contact of Acme's"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"), None)),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(1, TenantId("globex"))), Nil), "Ann shares Acme's contact with Globex"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"), Some(100))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), "Ann shares it with Globex until 100"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(2, TenantId("acme"), None)),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(2, TenantId("acme"))), Nil), "Ann cannot share Globex's deal with herself"),
    reject(CrmStore(List(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(Nil, Nil, Nil),
      "a write never removes another company's record"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), List(Share(1, TenantId("globex"))), Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Unshare(1, TenantId("globex"))),
      CrmStore(Nil, List(Share(1, TenantId("globex"))), Nil), "a share is never left without its record"))
  .exempt(noCrossTenantRead, "the store a write returns goes to the write side's storage, never to a reader: reads go through ReadContract")

/** A write: the change, when its author's company may make it; otherwise nothing changes. */
val applyWrite = define { (s: CrmStore, w: WriteCmd) =>
  w.change match
    case Change.Add(r) =>
      if r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id) then CrmStore(s.records ++ List(r), s.shares, s.expiries) else s
    case Change.ShareWith(id, to, until) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
        CrmStore(s.records, s.shares.filter(sh => sh != Share(id, to)) ++ List(Share(id, to)),
          s.expiries.filter(e => !(e.record == id && e.to == to)) ++ (until match
            case Some(u) => List(Expiry(id, to, u))
            case None    => Nil))
      else s
    case Change.Unshare(id, to) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
        CrmStore(s.records, s.shares.filter(sh => sh != Share(id, to)), s.expiries.filter(e => !(e.record == id && e.to == to)))
      else s
}

/** What the database is trusted to do with a write: store what a store holds about one record. */
val storeEdits = Node.port[BigInt, CrmStore, CrmStore](
  "StoreEdits",
  "Storing what a store holds about one record replaces what is stored about it: read back, the rows about it are what the store holds about it.",
  why = "A write changes only its own record's rows (WriteContract), so storing those rows is storing the write, whatever the size of the store. The rows are read back after storing: a write the database dropped or changed is seen on the call."
)((id, t, back) => back == aboutRecord(t, id))
  .examples(database.bind(Db.of(Nil, Nil)))(
    expect(BigInt(1), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(1, TenantId("globex"))), Nil),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), Nil), "the record and its share, not the other record"),
    expect(BigInt(3), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), CrmStore(Nil, Nil, Nil), "nothing is held about record 3"),
    reject(BigInt(1), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), Nil),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a share the database dropped is seen"))
  .exempt(noCrossTenantRead, "it returns the rows it stored to the write side, never to a reader")

/** The rows about a record, as the port promises them: what the SQL is checked against. */
val storedAbout = define { (id: BigInt, t: CrmStore) => aboutRecord(t, id) }

/** The production wiring of writes, owned as a design decision: changes to it are reviewed. */
val writeSideWiring = writeContract.design(
  "WriteSideWiring",
  "The write side applies every write through service, which checks each new store against WriteContract, and stores the written record's rows through StoreEdits.",
  why = "Every write must go through service; keeping the wiring in one governed file makes a change to it visible."
)("src/main/scala/crm/WriteSide.scala")
  .exempt(noCrossTenantRead, "the write side hands the new store to storage and returns nothing to a reader: no record leaves it")

// ============================================================================
// Root: shares given until a time end then, by a job
// ============================================================================

/** Whether a share has ended by `now`, by the store's expiries. */
val ended = define { (sh: Share, s: CrmStore, now: BigInt) => s.expiries.exists(e => e.record == sh.record && e.to == sh.to && e.until <= now) }

/** Model: what a run of the expiry job, at a time, does to the store. */
val sharesExpire = Node.root[(CrmStore, BigInt) => CrmStore](
  "SharesExpire",
  "When the expiry job runs, exactly the shares that have ended are removed; the records and the other shares stay.",
  why = "The idea lets a company share a record until a given time; the job is what ends such shares, and it touches nothing else.",
  idea = "Expiring shares"
)(run => forall((s: CrmStore, now: BigInt) => run(s, now).records == s.records && run(s, now).shares == s.shares.filter(sh => !ended(sh, s, now))))

val expireJob = sharesExpire.contract[CrmStore, BigInt, CrmStore](
  "ExpireJob",
  "A run removes exactly the shares that have ended, keeps the records, and keeps a consistent store consistent.",
  why = "SharesExpire, for one run. Keeping the store consistent matters because the read side relies on it (Accounts relies on CrmWrites), and the job changes the store besides the writes."
)((s, now, t) => t.records == s.records && t.shares == s.shares.filter(sh => !ended(sh, s, now)) && (consistentStore(s) ==> consistentStore(t)))
  .examples()(
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("initech"))), Nil), "Globex's share ended at 100; Initech's stays"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), 50,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), "before 100 nothing ends"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a share that has not ended is never removed"))
  .exempt(noCrossTenantRead, "the store it returns goes to storage, never to a reader")

/** A run: the shares that have not ended. */
val expire = define { (s: CrmStore, now: BigInt) =>
  CrmStore(s.records, s.shares.filter(sh => !ended(sh, s, now)), s.expiries.filter(e => !ended(Share(e.record, e.to), s, now)))
}

/** The job's wiring, owned as a design decision. */
val expiryJobWiring = expireJob.design(
  "ExpiryJobWiring",
  "The expiry job runs every minute through service, on the stored records, shares and expiries, and stores what it changed through StoreEdits.",
  why = "Every change to the store goes through a proven contract; keeping the job's wiring in one governed file makes a change to it visible."
)("src/main/scala/crm/Job.scala")
  .exempt(noCrossTenantRead, "it hands the new store to storage and returns nothing to a reader")

/** The HTTP API, owned as a design decision: every request goes through the read, deal and write sides. */
val httpApi = readContract.design(
  "HttpApi",
  "The HTTP API answers searches through the read side, the sales screen through the deal side, and writes through the write side; who calls is the account in the request's headers.",
  why = "Every request must reach the records only through service. Authentication is not modelled: the headers name the account."
)("src/main/scala/crm/Server.scala")
  .exempt(noCrossTenantRead, "it returns only what the read and deal sides return, which keep the rule")

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract, readSideWiring, noCrossTenantRead,
  recordsByQuery, writesKeepStore, stepByStep, crmWrites, writeContract, storeEdits, writeSideWiring, salesScreen, dealSearch,
  sharesExpire, expireJob, expiryJobWiring, httpApi)
  .implementProven(recordsByQuery)(storedMatching, (u, q) => database.value.recordsMatching(q))
  .implementProven(storeEdits)(storedAbout, (id, t) => database.value.storeAbout(id, t))
  .implementProven(expireJob)(expire)
  .implementProven(readContract)(search)
  .implementProven(dealSearch)(deals)
  .implementProven(writeContract)(applyWrite)

@main def crmCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/crm"))
