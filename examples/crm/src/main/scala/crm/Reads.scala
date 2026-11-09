package crm

import frflow.*

// ============================================================================
// Finding records: what a search returns, on either screen
// ============================================================================

val visibility = Node.claim("A search returns exactly the stored records it asks for that the user may read now.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    results(u, q).contains(r) === (held.records.contains(r) && askMatches(q, r) && mayReadNow(u, r))))
  .refines(sharedCrm, addedIsFound, writesLeaveOthers)
  .assuming(keyedTables, runsOneAtATime)

val noCrossTenantRead = Node.claim("No search, on either screen, returns a record the user may not read now.")(
  forall((u: Term[Account], q: Term[Search]) =>
    onlyReadable(held, clock, u, read(u, q).result) &&
      onlyReadable(held, clock, u, deals(u, q).result)))
  .assuming(keyedTables, runsOneAtATime)

// ============================================================================
// What a screen's results are: each a list, read against the store and the time
// ============================================================================

/** Whether every record of a list is one the store holds that the search matches. */
val onlyMatching = define { (s: Term[CrmStore], q: Term[Search], rs: Term[List[CrmRecord]]) =>
  rs.forall(r => s.records.contains(r) && matches(q, r)) }

/** Whether a list holds every record the store holds that the search matches. */
val allMatching = define { (s: Term[CrmStore], q: Term[Search], rs: Term[List[CrmRecord]]) =>
  s.records.forall(r => matches(q, r) implies rs.contains(r)) }

/** Whether a reader may read every record of a list, by a store at a time. */
val onlyReadable = define {
  (s: Term[CrmStore], now: Term[BigInt], reader: Term[Account], rs: Term[List[CrmRecord]]) =>
    rs.forall(r => mayRead(s, now, reader, r)) }

/** Whether a list holds every record the store holds that the search matches and the reader may read then. */
val allReadable = define {
  (s: Term[CrmStore], now: Term[BigInt], reader: Term[Account], q: Term[Search], rs: Term[List[CrmRecord]]) =>
    s.records.forall(r => (matches(q, r) && mayRead(s, now, reader, r)) implies rs.contains(r)) }

/** Whether every record of a list is a deal. */
val onlyDeals = define { (rs: Term[List[CrmRecord]]) => rs.forall(r => r.kind === (Kind.Deal: Kind)) }

/** Whether a list holds every deal the store holds that the search matches and the reader may read then. */
val allReadableDeals = define {
  (s: Term[CrmStore], now: Term[BigInt], reader: Term[Account], q: Term[Search], rs: Term[List[CrmRecord]]) =>
    s.records.forall(r =>
      (r.kind === (Kind.Deal: Kind) && matches(q, r) && mayRead(s, now, reader, r)) implies rs.contains(r)) }

// ============================================================================
// The records screen
// ============================================================================

val readContract = Node.claim("A search on the records screen returns exactly the stored records that match it and " +
    "the user may read now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    val got = read(user, query).result
    onlyMatching(held, query, got) &&
      onlyReadable(held, clock, user, got) &&
      allReadable(held, clock, user, query, got)))
  .refines(visibility)
  .assuming(keyedTables, runsOneAtATime)

val readsOnlyMatching = Node.claim("The records screen returns only stored records that match the search.")(
  forall((user: Term[Account], query: Term[Search]) => onlyMatching(held, query, read(user, query).result)))
  .refines(readContract)
  .assuming(keyedTables, runsOneAtATime)

val readsOnlyReadable = Node.claim("The records screen returns only records the user may read now.")(
  forall((user: Term[Account], query: Term[Search]) => onlyReadable(held, clock, user, read(user, query).result)))
  .refines(readContract, noCrossTenantRead)
  .assuming(keyedTables, runsOneAtATime)

val readsAllReadable = Node.claim("The records screen returns every stored record that matches the search and the " +
    "user may read now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    allReadable(held, clock, user, query, read(user, query).result)))
  .refines(readContract)
  .assuming(keyedTables, runsOneAtATime)

/** A search on the database at the time now: what the database returns for it, of the user's company or shared with
  * it then, by the shares and expiries it holds.
  */
def readSteps(user: Term[Account], query: Term[Search]): Flow[List[CrmRecord]] =
  for
    now <- Clock.now
    s   <- load
    rs  <- fetch(user, query)
  yield rs.filter(r => mayRead(s, now, user, r))

/** The records screen's search. */
val search = program { (user: Term[Account], query: Term[Search]) => readSteps(user, query) }

// ============================================================================
// The sales screen
// ============================================================================

val dealSearch = Node.claim("A deal search returns exactly the stored deals that match it and the user may read now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    val got = deals(user, query).result
    onlyMatching(held, query, got) &&
      onlyDeals(got) &&
      onlyReadable(held, clock, user, got) &&
      allReadableDeals(held, clock, user, query, got)))
  .refines(visibility)
  .assuming(keyedTables, runsOneAtATime)

val dealsOnlyMatching = Node.claim("The sales screen returns only stored records that match the search.")(
  forall((user: Term[Account], query: Term[Search]) => onlyMatching(held, query, deals(user, query).result)))
  .refines(dealSearch)
  .assuming(keyedTables, runsOneAtATime)

val dealsOnlyDeals = Node.claim("The sales screen returns only deals.")(
  forall((user: Term[Account], query: Term[Search]) => onlyDeals(deals(user, query).result)))
  .refines(dealSearch)
  .assuming(keyedTables, runsOneAtATime)

val dealsOnlyReadable = Node.claim("The sales screen returns only records the user may read now.")(
  forall((user: Term[Account], query: Term[Search]) => onlyReadable(held, clock, user, deals(user, query).result)))
  .refines(dealSearch, noCrossTenantRead)
  .assuming(keyedTables, runsOneAtATime)

val dealsAllReadable = Node.claim("The sales screen returns every stored deal that matches the search and the user " +
    "may read now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    allReadableDeals(held, clock, user, query, deals(user, query).result)))
  .refines(dealSearch)
  .assuming(keyedTables, runsOneAtATime)

/** Deals: what the records screen's search returns, keeping only deals. */
val dealsOf = program { (user: Term[Account], query: Term[Search]) =>
  readSteps(user, query).map(rs => rs.filter(r => r.kind === (Kind.Deal: Kind))) }

val readSideWiring = Node.design("The records screen and the sales screen run their proven code on the clock and " +
    "the SQLite database.")(
  "src/main/scala/crm/ReadSide.scala")
  .refines(readContract, dealSearch)
