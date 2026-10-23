package crm

import frflow.*

// ============================================================================
// Finding records: what a search returns, on either screen
// ============================================================================

val visibility = Node.claim("Visibility",
  "A search, on either screen, returns exactly the stored records it asks for that the user may read now: of their company, or shared with it now.",
  why = "The read side of the purpose: what a user finds is what the screens return, of what the CRM holds now (CrmRun), its shares counted until their time. With StoreMirrorsRequests, what the CRM holds is what users asked, so a search finds what the purpose says.",
  idea = "Finding records"
)(forall((u: Account, q: Ask) => forall((r: CrmRecord) => results(u, q).contains(r) == (store.value.contains(r) && askMatches(q, r) && mayRead(u, r)))))
  .under(sharedCrm)

/** One rule for every read path, stated once: a reader is shown a record only if their company may see it. */
val noCrossTenantRead = Node.invariant[Account, CrmRecord](
  "NoCrossTenantRead",
  "No search returns a record of another company unless that company shared it with the reader's, for good or until a time not yet come.",
  why = "The isolation every read path must keep, stated once. Every contract keeps it, listing the records a call shows to whom, or says why it shows none; so a new read path (an export, an admin view) cannot leave it out unnoticed.",
  idea = "Finding records"
)((reader, r) => mayRead(reader, r))
  .under(visibility)

val searchesMatch = Node.claim("SearchesMatch",
  "A search, on either screen, returns only stored records it asks for, and every stored record it asks for that the user may read.",
  why = "Users find records by id, by kind, or by listing everything, on the records screen or on the sales screen, which lists deals only: a search returns what it asks for, all of it that the user may read. That it returns nothing else to read is NoCrossTenantRead's.",
  idea = "Finding records"
)(forall((u: Account, q: Ask) => results(u, q).forall(r => store.value.contains(r) && askMatches(q, r)) &&
  store.value.forall(r => (askMatches(q, r) && mayRead(u, r)) ==> results(u, q).contains(r))))
  .under(visibility)

// ============================================================================
// Port: the database's answer to a search
// ============================================================================

/** What the database is trusted to do: return exactly the stored records a search asks for. */
val recordsByQuery = Node.assumption(fetch)("RecordsByQuery",
  "The database returns exactly the stored records that match a search, of every company.",
  why = "Records live in SQLite. The read side is proven from this promise, not from the SQL; the SQL is checked against the define the port is decided with on its examples and on varied data, and every result it returns is checked to match the search."
)((user, query, rs) => rs.forall(r => store.value.contains(r) && matches(query, r)) && store.value.forall(r => matches(query, r) ==> rs.contains(r)))
  .checkedBy((user, query, rs) => rs.forall(r => matches(query, r)))
  .examples(
    history.bind(List(
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.Add(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")))),
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(3, TenantId("acme"), Kind.Contact, "Acme contact")))))),
    database.bind(Db.replaying(history.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact),
      List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"), CrmRecord(3, TenantId("acme"), Kind.Contact, "Acme contact")),
      "every company's contacts: the database does not filter by company, the read side does"),
    expect(Account("ann@acme", TenantId("acme")), Search.ById(1), List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), "a record by its id"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "a stored record is never left out"))

/** The records a search asks for, as the port promises them: what the SQL is checked against. */
val storedMatching = define { (user: Account, query: Search) => store.value.filter(r => matches(query, r)) }

// ============================================================================
// Contracts: the records screen and the sales screen
// ============================================================================

val readContract = Node.contract(read)("ReadContract",
  "A search on the records screen returns exactly the stored records that match it and the user may read: each of the user's company or shared with it now.",
  why = "The records screen, stated for one call. A returned record must be one of the stored records, so code cannot relabel another company's record as the user's; and every such record is returned, since users find records.",
  idea = "Finding records"
)((user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .under(searchesMatch)
  .examples(
    history.bind(List(
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.Add(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")))))),
    clock.bind(BigInt(0)), database.bind(Db.replaying(history.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "Ann lists everything she can see: the deal she added"),
    expect(Account("ann@acme", TenantId("acme")), Search.ById(2), Nil, "Globex's contact is not shared with Acme"),
    reject(Account("ann@acme", TenantId("acme")), Search.ById(2), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "another company's record is never returned"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(2, TenantId("acme"), Kind.Contact, "Globex contact")),
      "a record relabelled as Acme's is not a stored record"),
    reject(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "a search for contacts does not return deals"))
  .examples(
    history.bind(List(
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.Add(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.ShareWith(2, TenantId("acme"), Some(100)))))),
    clock.bind(BigInt(50)), database.bind(Db.replaying(history.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "Globex shared its contact with Acme until 100: at 50 Ann finds it by kind"))
  .examples(
    history.bind(List(
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.Add(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")))),
      Event.Wrote(WriteCmd(Account("gil@globex", TenantId("globex")), Change.ShareWith(2, TenantId("acme"), Some(100)))))),
    clock.bind(BigInt(150)), database.bind(Db.replaying(history.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), Nil,
      "at 150 the share has ended, though the expiry job has not run: Ann no longer finds the contact"),
    reject(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
      "a share past its time never shows the record"))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))
  .checkedBy((user, query, result) => result.forall(r => matches(query, r) && mayRead(user, r)))
  .expects("Someone at Acme never sees a Globex record that Globex did not share with Acme, whatever they search for")(
    forall((u: Account, q: Search) => (u.tenant == TenantId("acme")) ==>
      read(u, q).forall(r => (r.tenant == TenantId("globex")) ==> shares.value.contains(Share(r.id, TenantId("acme"))))))

/** A search: what the database returns for it, of the user's company or shared with it now. */
val search = define { (user: Account, query: Search) => fetch(user, query).filter(r => mayRead(user, r)) }

val dealSearch = Node.contract(deals)("DealSearch",
  "A deal search returns exactly the stored deals that match it and the user may read.",
  why = "The sales screen, stated for one call. Its code calls the records screen and keeps the deals, so it is proven from ReadContract's promise and shows only what the records screen may show.",
  idea = "Sales screen"
)((user, query, result) => result.forall(r => store.value.contains(r) && r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .under(searchesMatch)
  .examples(
    history.bind(List(
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")))),
      Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact")))))),
    clock.bind(BigInt(0)), database.bind(Db.replaying(history.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")),
      "Ann's deal search lists Acme's deal, not its contact"),
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), Nil, "a search for contacts finds no deal"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, List(CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact")),
      "a contact is never listed as a deal"),
    reject(Account("ann@acme", TenantId("acme")), Search.Everything, Nil, "a deal Ann may see is never left out"))
  .keeps(noCrossTenantRead)((user, query, result) => result.map(r => (user, r)))

/** Deals: what the records screen returns, keeping only deals. */
val dealsOf = define { (user: Account, query: Search) => read(user, query).filter(r => r.kind == Kind.Deal) }

/** The production wiring of reads, owned as a design decision: changes to it are reviewed. */
val readSideWiring = Node.design(
  "ReadSideWiring",
  "The records screen and the sales screen serve searches through service, which checks every result against ReadContract or DealSearch and the invariant they keep; they read the store, shares and expiries from the database's tables, the history from its event log, and the clock.",
  why = "Every path to the records must go through service; keeping the wiring in one governed file makes a change to it visible. The tables are bound as they are, not replayed from the event log on every search: they hold what the history led to (CrmRun) because only the write side and the expiry job change them, each also logging its event."
)("src/main/scala/crm/ReadSide.scala")
  .under(readContract, dealSearch)
  .exempt(noCrossTenantRead, "it returns no records itself: every read goes through service, which checks each result against the contract and the invariant")
