package crm

import frflow.*

// ============================================================================
// Finding records: what a search returns, on either screen
// ============================================================================

val visibility = Node.claim("Visibility",
  "A search, on either screen, returns exactly the stored records it asks for that belong to the user's company or are shared with it.",
  why = "The purpose's first half, in the domain's words: what a user finds is what the screens return, and a record they may read is one of their company or one shared with it.",
  idea = "Finding records"
)(forall((u: Account, q: Ask) => forall((r: CrmRecord) => results(u, q).contains(r) == (store.value.contains(r) && askMatches(q, r) && mayRead(u, r)))))
  .under(sharedCrm)

/** One rule for every read path, stated once: a reader is shown a record only if their company may see it. */
val noCrossTenantRead = Node.invariant[Account, CrmRecord](
  "NoCrossTenantRead",
  "No search returns a record of another company unless that company shared it with the reader's.",
  why = "The isolation every read path must keep, stated once. Every contract keeps it, listing the records a call shows to whom, or says why it shows none; so a new read path (an export, an admin view) cannot leave it out unnoticed.",
  idea = "Finding records"
)((reader, r) => mayRead(reader, r))
  .under(visibility)

val findRecords = Node.claim("FindRecords",
  "A search on the records screen returns only stored records that match it, and every stored record matching it that the user may read.",
  why = "Users find records by id, by kind, or by listing everything: a search returns what it asks for, all of it that the user may read. That it returns nothing else to read is NoCrossTenantRead's.",
  idea = "Finding records"
)(forall((u: Account, q: Search) => read(u, q).forall(r => store.value.contains(r) && matches(q, r)) &&
  store.value.forall(r => (matches(q, r) && mayRead(u, r)) ==> read(u, q).contains(r))))
  .under(visibility)

val salesScreen = Node.claim("SalesScreen",
  "The sales screen returns only stored deals that match the search, and every stored deal matching it that the user may read.",
  why = "The sales team's screen lists deals only, and every deal they may see; that it shows nothing else to read is NoCrossTenantRead's.",
  idea = "Sales screen"
)(forall((u: Account, q: Search) => deals(u, q).forall(r => store.value.contains(r) && r.kind == Kind.Deal && matches(q, r)) &&
  store.value.forall(r => (r.kind == Kind.Deal && matches(q, r) && mayRead(u, r)) ==> deals(u, q).contains(r))))
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
    store.bind(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact"))),
    database.bind(Db.of(store.value)))(
    expect(Account("ann@acme", TenantId("acme")), Search.OfKind(Kind.Contact), List(CrmRecord(2, TenantId("globex"), Kind.Contact, "Globex contact")),
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
  "A search returns exactly the stored records that match it and the user may read: each of the user's company or shared with it.",
  why = "The records screen, stated for one call. A returned record must be one of the stored records, so code cannot relabel another company's record as the user's; and every such record is returned, since users find records.",
  idea = "Finding records"
)((user, query, result) => result.forall(r => store.value.contains(r) && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .under(findRecords)
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
  .expects("Someone at Acme never sees a Globex record that Globex did not share with Acme, whatever they search for")(
    forall((u: Account, q: Search) => (u.tenant == TenantId("acme")) ==>
      read(u, q).forall(r => (r.tenant == TenantId("globex")) ==> shares.value.contains(Share(r.id, TenantId("acme"))))))

/** A search: what the database returns for it, of the user's company or shared with it. */
val search = define { (user: Account, query: Search) => fetch(user, query).filter(r => mayRead(user, r)) }

val dealSearch = Node.contract(deals)("DealSearch",
  "A deal search returns exactly the stored deals that match it and the user may read.",
  why = "The sales screen, stated for one call. Its code calls the records screen and keeps the deals, so it is proven from ReadContract's promise and shows only what the records screen may show.",
  idea = "Sales screen"
)((user, query, result) => result.forall(r => store.value.contains(r) && r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) &&
  store.value.forall(r => (r.kind == Kind.Deal && matches(query, r) && mayRead(user, r)) ==> result.contains(r)))
  .under(salesScreen)
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

/** Deals: what the records screen returns, keeping only deals. */
val dealsOf = define { (user: Account, query: Search) => read(user, query).filter(r => r.kind == Kind.Deal) }

/** The production wiring of reads, owned as a design decision: changes to it are reviewed. */
val readSideWiring = Node.design(
  "ReadSideWiring",
  "The records screen and the sales screen serve searches through service, which checks every result against ReadContract or DealSearch and the invariant they keep.",
  why = "Every path to the records must go through service; keeping the wiring in one governed file makes a change to it visible."
)("src/main/scala/crm/ReadSide.scala")
  .under(readContract, dealSearch)
  .exempt(noCrossTenantRead, "it returns no records itself: every read goes through service, which checks each result against the contract and the invariant")
