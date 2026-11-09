package crm

import frflow.*

// ============================================================================
// What users asked: the history of adds, shares and unshares, with their times
// ============================================================================

/** Whether users have asked for a record of that id of the write's author's company. */
val ownIn = define { (a: Term[Asked], w: Term[WriteCmd], id: Term[BigInt]) =>
  a.records.exists(x => x.id === id && x.tenant === w.by.tenant) }

/** The grants asked but the one of the record with the company. */
val grantsBut = define { (a: Term[Asked], id: Term[BigInt], to: Term[TenantId]) =>
  a.grants.filter(g => !(g.record === id && g.to === to)) }

/** Whether a grant still stands at `now`: it is for good, or its time comes after `now`. */
val grantStands = define { (g: Term[Grant], now: Term[BigInt]) => g.until.forall(t => now < t) }

/** An add, as users asked it: the record added, when it is of the author's company under an id not asked before. */
val askedAdd = define { (a: Term[Asked], w: Term[WriteCmd], r: Term[CrmRecord]) =>
  when(r.tenant === w.by.tenant && !a.records.exists(x => x.id === r.id))(
    make[Asked](a.records :+ r, a.grants)).otherwise(a) }

/** A share, as users asked it: the grant replacing the record's grant to the company, when the record is the
  * author's company's.
  */
val askedShare = define {
  (a: Term[Asked], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]]) =>
    when(ownIn(a, w, id))(make[Asked](a.records, grantsBut(a, id, to) :+ make[Grant](id, to, until))).otherwise(a) }

/** An unshare, as users asked it: the record's grant to the company gone, when the record is the author's company's. */
val askedUnshare = define { (a: Term[Asked], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId]) =>
  when(ownIn(a, w, id))(make[Asked](a.records, grantsBut(a, id, to))).otherwise(a) }

/** A run of the expiry job, as users asked it: the grants that still stand at its time. */
val askedExpiry = define { (a: Term[Asked], now: Term[BigInt]) =>
  make[Asked](a.records, a.grants.filter(g => grantStands(g, now))) }

/** One more event, as users asked it. */
val askedStep = define { (a: Term[Asked], e: Term[Event]) =>
  e.on[Event.Wrote](w => w.change
      .on[Change.Add](r => askedAdd(a, w, r))
      .on[Change.ShareWith]((id, to, until) => askedShare(a, w, id, to, until))
      .on[Change.Unshare]((id, to) => askedUnshare(a, w, id, to)))
    .on[Event.Expired](now => askedExpiry(a, now)) }

/** What a history asked, from nothing asked, each event in turn. */
val askedIn = define { (es: Term[List[Event]]) =>
  es.foldLeft(make[Asked](Nil: Term[List[CrmRecord]], Nil: Term[List[Grant]]))((a, e) => askedStep(a, e)) }

/** Whether what a history asked shares the record with the company at `now`. */
val sharedIn = define { (es: Term[List[Event]], id: Term[BigInt], c: Term[TenantId], now: Term[BigInt]) =>
  askedIn(es).grants.exists(g => g.record === id && g.to === c && grantStands(g, now)) }

// The tables hold one row per key (owner §40): what the stores from outside meet
val keyedTables = Node.assumption("The database's tables hold one row per key.")(
  always[CrmStore](s => onePerKey(s)))

/** The event of a user's write adding a record. */
val addOf = define { (u: Term[Account], r: Term[CrmRecord]) =>
  make[Event.Wrote](make[WriteCmd](u, make[Change.Add](r))) }

/** Whether a user may add a record after a history: it is of their company, under an id no record added before has. */
val addable = define { (es: Term[List[Event]], u: Term[Account], r: Term[CrmRecord]) =>
  r.tenant === u.tenant && !askedIn(es).records.exists(x => x.id === r.id) }

/** Whether a history is `pre`, then the user's add of the record, which they could make then, then `post`. */
val addsAt = define {
  (hs: Term[List[Event]], pre: Term[List[Event]], post: Term[List[Event]], u: Term[Account], r: Term[CrmRecord]) =>
    hs === pre ++ (addOf(u, r) :: post) && addable(pre, u, r) }

/** Whether, after a history, a reader may read the record at `now`: it is of their company, or shared with it then. */
val readableIn = define { (es: Term[List[Event]], now: Term[BigInt], reader: Term[Account], r: Term[CrmRecord]) =>
  r.tenant === reader.tenant || sharedIn(es, r.id, reader.tenant, now) }

/** Whether a history entitles a user's search at `now` to find a record: the search asks for it, the history added
  * it, and the user may read it then.
  */
val entitled = define {
  (es: Term[List[Event]], now: Term[BigInt], u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    askMatches(q, r) && askedIn(es).records.contains(r) && readableIn(es, now, u, r) }

// ============================================================================
// Two roots of their own (owner §22): what a user can count on, each proven from what a search returns and what
// the CRM holds (`visibility`, `storeMirrorsRequests`)
// ============================================================================

val addedIsFound = Node.claim("A record a user could add is, once added, found by each of their searches that asks " +
    "for it.")(
  forall((u: Term[Account], r: Term[CrmRecord], pre: Term[List[Event]], post: Term[List[Event]], q: Term[Ask]) =>
    (addsAt(history, pre, post, u, r) && askMatches(q, r)) implies results(u, q).contains(r)))
  .assuming(keyedTables, runsOneAtATime)

val writesLeaveOthers = Node.claim("Just after a user's write, a search finds another company's record exactly when " +
    "the history before the write entitled it to.")(
  forall((es: Term[List[Event]], w: Term[WriteCmd], u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    (history === es :+ make[Event.Wrote](w) && r.tenant =!= w.by.tenant) implies
      (results(u, q).contains(r) === entitled(es, clock, u, q, r))))
  .assuming(keyedTables, runsOneAtATime)

// ============================================================================
// The root: what a user's search finds, of what users asked
// ============================================================================

val sharedCrm = Node.claim("A user's search finds exactly the added records it asks for that the user may read.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    finds(u, q, r) === (asksFor(q, r) && added(owner(r), r) && readable(u, r))))
  .assuming(keyedTables)

// ============================================================================
// The purpose's words, each one equation
// ============================================================================

val companies = Node.claim("A user's company is the one their account names.")(
  forall((a: Term[Account]) => companyOf(a) === a.tenant))
  .refines(sharedCrm)

val ownership = Node.claim("A record belongs to the company stored on it.")(
  forall((r: Term[CrmRecord]) => owner(r) === r.tenant))
  .refines(sharedCrm)

val searches = Node.claim("A user's search finds what its screen returns for it now.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) => finds(u, q, r).current === results(u, q).contains(r)))
  .refines(sharedCrm)

val searchesAsk = Node.claim("A search asks for the records it matches on its screen.")(
  forall((q: Term[Ask], r: Term[CrmRecord]) => asksFor(q, r) === askMatches(q, r)))
  .refines(sharedCrm)

val readers = Node.claim("A user may read a record exactly when it is their company's or shared with it now.")(
  forall((u: Term[Account], r: Term[CrmRecord]) =>
    readable(u, r) === (owner(r) === companyOf(u) || sharedWith(r, companyOf(u)))))
  .refines(sharedCrm)

val adding = Node.claim("A company has added a record exactly when the record is the company's and the CRM's " +
    "history added it.")(
  forall((c: Term[TenantId], r: Term[CrmRecord]) =>
    added(c, r) === (r.tenant === c && askedIn(history).records.contains(r))))
  .refines(sharedCrm)

val sharing = Node.claim("A record is shared with a company now exactly when the CRM's history shares it with " +
    "that company now.")(
  forall((r: Term[CrmRecord], c: Term[TenantId]) => sharedWith(r, c) === sharedIn(history, r.id, c, clock)))
  .refines(sharedCrm)
