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

/** A user may see a record of their own company, or one shared with it. */
val visible = define { (u: User.T, r: Record.T) => owner(r) == tenantOf(u) || sharedWith(r, tenantOf(u)) }

/** Model: whom the system shows which records. */
val isolation = Node.root[(User.T, Record.T) => Boolean](
  "TenantIsolation",
  "A user sees a record only if it belongs to their company or was shared with their company.",
  why = "Isolation between companies is what the idea says must hold. Companies, users, records and sharing are left open.",
  idea = "Reading records"
)(shows => forall((u: User.T, r: Record.T) => shows(u, r) ==> visible(u, r)))

// ============================================================================
// Users see records only through queries
// ============================================================================

val Query = Opaque("Query", "a search a user runs")

/** Model: what a query returns to a user. */
val readApi = isolation.refine[(User.T, Query.T) => List[Record.T]](
  "ReadApi",
  "Records are shown only as query results, and a query returns only records the user may see.",
  why = "Users find records by searching, so what a user sees is what their queries return. abs: a user is shown a record when some query of theirs returns it."
)(
  abs  = run => (u, r) => exists((q: Query.T) => run(u, q).contains(r)),
  spec = run => forall((u: User.T, q: Query.T) => run(u, q).forall(r => visible(u, r)))
)

// ============================================================================
// Instantiation: the concrete CRM domain
// ============================================================================

final case class TenantId(value: String)
final case class Account(email: String, tenant: TenantId)

enum Kind:
  case Contact, Deal

final case class CrmRecord(id: Long, tenant: TenantId, kind: Kind, title: String)
final case class Share(record: Long, to: TenantId)

enum Search:
  case ById(id: Long)
  case OfKind(kind: Kind)
  case Everything

val shares = Param[List[Share]]("shares", "the share table as stored when the search runs; a share names a record by its id, which is unique across all companies (in every store writes reach: WritesKeepStore)")

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
  sharedWith := ((r: CrmRecord, t: TenantId) => shares.value.contains(Share(r.id, t)))
)

// ============================================================================
// Contract for implementations
// ============================================================================

val store = Param[List[CrmRecord]]("store", "the records as stored when the search runs")

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

val readContract = accounts.contract[Account, Search, List[CrmRecord]](
  "ReadContract",
  "A search returns exactly the stored records that match it and the user may see: each of the user's company or shared with it.",
  why = "Accounts, stated for one call, plus what a search asks for. A returned record must be one of the stored records, so an implementation cannot relabel another company's record as the user's; and every such record is returned, since the idea says users find records."
)((user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .examples(
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    shares.bind(Nil))(
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
    shares.bind(List(Share(2, TenantId("acme")))))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "Globex shared its contact with Acme, so Ann finds it by kind"))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))
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

/** A search: the stored records it asks for, of the user's company or shared with it. */
val search = define { (user: Account, query: Search) =>
  store.value.filter(r => matches(query, r) && mayRead(user, r))
}

// ============================================================================
// Root: writes keep the store consistent, and touch only the author's company
// ============================================================================

val Store = Opaque("Store", "the records and shares as stored")
val Write = Opaque("Write", "a change a user asks for: adding a record, or sharing or unsharing one")

val initial    = Param[Store.T]("initial", "the store the CRM starts with")
val consistent = Param[Store.T => Boolean]("consistent", "whether every share is of a stored record, and no two records have one id")
val permitted  = Param[(Store.T, Write.T, Store.T) => Boolean]("permitted",
  "whether the change from the first store to the second is one the write's author may make: it touches only their company's records and shares")

/** Model: the store a sequence of writes leads to, from the initial store. */
val writesKeepStore = Node.root[List[Write.T] => Store.T](
  "WritesKeepStore",
  "Every store the CRM reaches by writes is consistent, and every write changes only what its author's company may change.",
  why = "The idea's rules for writing, over every sequence of writes from the initial store: consistency of every store reached, and authority of each write. What consistency and authority mean is left open.",
  idea = "Writing records"
)(run => forall((ws: List[Write.T]) => consistent(run(ws))) &&
  forall((ws: List[Write.T], w: Write.T) => permitted(run(ws), w, run(ws ++ List(w)))))

/** Model: one write. */
val stepByStep = writesKeepStore.refine[(Store.T, Write.T) => Store.T](
  "StepByStep",
  "The CRM starts consistent, a write keeps a consistent store consistent, and every write is permitted.",
  why = "A store is reached by applying writes one at a time from the initial store, so it is enough that the initial store is consistent and that each write keeps consistency (by induction over the writes) and is permitted. abs: the store after a sequence of writes is the writes applied in turn."
)(
  abs = apply => ws => ws.foldLeft(initial.value)((s, w) => apply(s, w)),
  spec = apply => consistent(initial.value) && forall((s: Store.T, w: Write.T) => (consistent(s) ==> consistent(apply(s, w))) && permitted(s, w, apply(s, w))))

final case class CrmStore(records: List[CrmRecord], shares: List[Share])

enum Change:
  case Add(record: CrmRecord)
  case ShareWith(record: Long, to: TenantId)
  case Unshare(record: Long, to: TenantId)

final case class WriteCmd(by: Account, change: Change)

/** A consistent store: every share is of a stored record, and no two records have one id. */
val consistentStore = define { (s: CrmStore) =>
  s.shares.forall(sh => s.records.exists(r => r.id == sh.record)) && s.records.forall(a => s.records.forall(b => (a.id == b.id) ==> (a == b)))
}

/** What a permitted write does: an Add of a record of the author's company with a fresh id stores it; a
  * share or unshare of a record of the author's company is made.
  */
val takesEffect = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  w.change match
    case Change.Add(r) => (r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id)) ==> t.records.contains(r)
    case Change.ShareWith(id, to) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==> t.shares.contains(Share(id, to))
    case Change.Unshare(id, to) => s.records.exists(x => x.id == id && x.tenant == w.by.tenant) ==> !t.shares.contains(Share(id, to))
}

/** What a write may change: only its author's company's records, and only shares of their company's records. */
val permittedWrite = define { (s: CrmStore, w: WriteCmd, t: CrmStore) =>
  t.records.filter(r => r.tenant != w.by.tenant) == s.records.filter(r => r.tenant != w.by.tenant) &&
  t.shares.forall(sh => s.shares.contains(sh) || t.records.exists(r => r.id == sh.record && r.tenant == w.by.tenant)) &&
  s.shares.forall(sh => t.shares.contains(sh) || s.records.exists(r => r.id == sh.record && r.tenant == w.by.tenant))
}

val crmWrites = stepByStep.instantiate[(CrmStore, WriteCmd) => CrmStore](
  "CrmWrites",
  "The store is the CRM's records and shares; a write is a user's change; a store is consistent when every share is of a stored record and record ids are unique; a write may change only its author's company's records, and add or remove only shares of their company's records.",
  why = "A share names a record by its id: a share of a record that is not stored would show the next record stored with that id, and two records with one id would both be shared by it, across companies. Authority is by the author's account, which authentication provides (not modelled). Records of other companies must come out of a write exactly as they went in."
)(
  Store      := of[CrmStore],
  Write      := of[WriteCmd],
  initial    := CrmStore(Nil, Nil),
  consistent := ((s: CrmStore) => consistentStore(s)),
  permitted  := ((s: CrmStore, w: WriteCmd, t: CrmStore) => permittedWrite(s, w, t))
)

val writeContract = crmWrites.contract[CrmStore, WriteCmd, CrmStore](
  "WriteContract",
  "A write keeps every share of a stored record and record ids unique, changes only the author's company's records and only shares of their company's records, and a write its author's company may make takes effect.",
  why = "CrmWrites, stated for one call, plus what the idea promises a user can do: add records for their company, and share or unshare them. A write the company may not make changes nothing."
)((s, w, t) => (consistentStore(s) ==> consistentStore(t)) && permittedWrite(s, w, t) && takesEffect(s, w, t))
  .examples()(
    expect(CrmStore(Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil),
      "Ann adds a contact of Acme's"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(1, TenantId("globex")))), "Ann shares Acme's contact with Globex"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(2, TenantId("acme"))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(2, TenantId("acme")))), "Ann cannot share Globex's deal with herself"),
    reject(CrmStore(List(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(Nil, Nil),
      "a write never removes another company's record"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), List(Share(1, TenantId("globex")))), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Unshare(1, TenantId("globex"))),
      CrmStore(Nil, List(Share(1, TenantId("globex")))), "a share is never left without its record"))
  .exempt(noCrossTenantRead, "the store a write returns goes to the write side's storage, never to a reader: reads go through ReadContract")

/** A write: the change, when its author's company may make it; otherwise nothing changes. */
val applyWrite = define { (s: CrmStore, w: WriteCmd) =>
  w.change match
    case Change.Add(r) =>
      if r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id) then s.copy(records = s.records ++ List(r)) else s
    case Change.ShareWith(id, to) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then s.copy(shares = s.shares ++ List(Share(id, to))) else s
    case Change.Unshare(id, to) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then s.copy(shares = s.shares.filter(sh => sh != Share(id, to))) else s
}

/** The production wiring of writes, owned as a design decision: changes to it are reviewed. */
val writeSideWiring = writeContract.design(
  "WriteSideWiring",
  "The write side applies every write through service, which checks each new store against WriteContract.",
  why = "Every write must go through service; keeping the wiring in one governed file makes a change to it visible."
)("src/main/scala/crm/WriteSide.scala")

val knowledge = KnowledgeBase("Crm", idea = "IDEA.md")(isolation, readApi, accounts, readContract, readSideWiring, noCrossTenantRead,
  writesKeepStore, stepByStep, crmWrites, writeContract, writeSideWiring)
  .implementProven(readContract)(search)
  .implementProven(writeContract)(applyWrite)

@main def crmCli(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/crm"))
