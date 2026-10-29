package crm

import frflow.*

// ============================================================================
// Finding records: what a search returns, on either screen
// ============================================================================

val visibility = Node.claim("A search, on either screen, returns exactly the stored records it asks for that the " +
    "user may read now: of their company, or shared with it now.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    results(u, q).contains(r) === (held.records.contains(r) && askMatches(q, r) && mayRead(u, r))))
  .refines(sharedCrm, addedIsFound, writesLeaveOthers)
  .assuming(crmRun)

val noCrossTenantRead = Node.claim("No search returns a record of another company unless that company shared it " +
    "with the reader's, for good or until a time not yet come.")(
  forall((u: Term[Account], q: Term[Search]) =>
    read(u, q).forall(r => mayRead(u, r)) && deals(u, q).forall(r => mayRead(u, r))))

val searchesMatch = Node.claim("A search, on either screen, returns only stored records it asks for, and every " +
    "stored record it asks for that the user may read.")(
  forall((u: Term[Account], q: Term[Ask]) => results(u, q).forall(r => held.records.contains(r) && askMatches(q, r)) &&
    held.records.forall(r => (askMatches(q, r) && mayRead(u, r)) implies results(u, q).contains(r))))
  .refines(visibility)

// ============================================================================
// The database's answer to a search
// ============================================================================

val recordsByQuery = Node.assumption("The database returns exactly the stored records that match a search, of " +
    "every company.")(
  forall((user: Term[Account], query: Term[Search]) =>
    fetch(user, query).forall(r => held.records.contains(r) && matches(query, r)) &&
      held.records.forall(r => matches(query, r) implies fetch(user, query).contains(r))))

// ============================================================================
// The records screen and the sales screen
// ============================================================================

val readContract = Node.claim("A search on the records screen returns exactly the stored records that match it and " +
    "the user may read: each of the user's company or shared with it now.")(
  forall((user: Term[Account], query: Term[Search]) =>
    read(user, query).forall(r => held.records.contains(r) && matches(query, r) && mayRead(user, r)) &&
      held.records.forall(r => (matches(query, r) && mayRead(user, r)) implies read(user, query).contains(r))))
  .refines(searchesMatch, noCrossTenantRead)

/** A search: what the database returns for it, of the user's company or shared with it now. */
val search = define { (user: Term[Account], query: Term[Search]) => fetch(user, query).filter(r => mayRead(user, r)) }

val dealSearch = Node.claim("A deal search returns exactly the stored deals that match it and the user may read.")(
  forall((user: Term[Account], query: Term[Search]) =>
    deals(user, query).forall(r =>
      held.records.contains(r) && r.kind === (Kind.Deal: Kind) && matches(query, r) && mayRead(user, r)) &&
      held.records.forall(r => (r.kind === (Kind.Deal: Kind) && matches(query, r) && mayRead(user, r)) implies
        deals(user, query).contains(r))))
  .refines(searchesMatch, noCrossTenantRead)

/** Deals: what the records screen returns, keeping only deals. */
val dealsOf = define { (user: Term[Account], query: Term[Search]) =>
  read(user, query).filter(r => r.kind === (Kind.Deal: Kind)) }

val readSideWiring = Node.design("The records screen and the sales screen serve searches through their code; they " +
    "read the store, shares and expiries from the database's tables, the history from its event log, and the clock.")(
  "src/main/scala/crm/ReadSide.scala")
  .refines(readContract, dealSearch)
