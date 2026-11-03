package crm

import frflow.*

// ============================================================================
// Finding records: what a search returns, on either screen
// ============================================================================

val visibility = Node.claim("A search, on either screen, returns exactly the stored records it asks for that the " +
    "user may read now: of their company, or shared with it now.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    results(u, q).contains(r) === (held.records.contains(r) && askMatches(q, r) && mayReadNow(u, r))))
  .refines(sharedCrm, addedIsFound, writesLeaveOthers)
  .assuming(keyedTables, runsOneAtATime)

val noCrossTenantRead = Node.claim("No search returns a record of another company unless that company shared it " +
    "with the reader's, for good or until a time not yet come.")(
  forall((u: Term[Account], q: Term[Search]) =>
    read(u, q).result.forall(r => mayReadNow(u, r)) && deals(u, q).result.forall(r => mayReadNow(u, r))))
  .assuming(keyedTables, runsOneAtATime)

val searchesMatch = Node.claim("A search, on either screen, returns only stored records it asks for, and every " +
    "stored record it asks for that the user may read.")(
  forall((u: Term[Account], q: Term[Ask]) => results(u, q).forall(r => held.records.contains(r) && askMatches(q, r)) &&
    held.records.forall(r => (askMatches(q, r) && mayReadNow(u, r)) implies results(u, q).contains(r))))
  .refines(visibility)
  .assuming(keyedTables, runsOneAtATime)

// ============================================================================
// The records screen and the sales screen
// ============================================================================

val readContract = Node.claim("A search on the records screen returns exactly the stored records that match it and " +
    "the user may read: each of the user's company or shared with it now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    read(user, query).result.forall(r => held.records.contains(r) && matches(query, r) && mayReadNow(user, r)) &&
      held.records.forall(r =>
        (matches(query, r) && mayReadNow(user, r)) implies read(user, query).result.contains(r))))
  .refines(searchesMatch, noCrossTenantRead)
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

val dealSearch = Node.claim("A deal search returns exactly the stored deals that match it and the user may read.")(
  forall((user: Term[Account], query: Term[Search]) =>
    deals(user, query).result.forall(r =>
      held.records.contains(r) && r.kind === (Kind.Deal: Kind) && matches(query, r) && mayReadNow(user, r)) &&
      held.records.forall(r => (r.kind === (Kind.Deal: Kind) && matches(query, r) && mayReadNow(user, r)) implies
        deals(user, query).result.contains(r))))
  .refines(searchesMatch, noCrossTenantRead)
  .assuming(keyedTables, runsOneAtATime)

/** Deals: what the records screen's search returns, keeping only deals. */
val dealsOf = program { (user: Term[Account], query: Term[Search]) =>
  readSteps(user, query).map(rs => rs.filter(r => r.kind === (Kind.Deal: Kind))) }

val readSideWiring = Node.design("The records screen and the sales screen serve searches through their code; they " +
    "read the time from the clock, the shares and expiries from the database's tables, and search them with SQL.")(
  "src/main/scala/crm/ReadSide.scala")
  .refines(readContract, dealSearch)
