package crm

import examples.Folds.*
import frflow.*

// ============================================================================
// What users asked: the history of adds, shares and unshares, with their times
// ============================================================================

/** One more event, as users asked it: an add of a record of its author's company under an id no record added before
  * had; a share or unshare, by a user of the company of the record with that id, which replaces or ends that
  * record's share with that company; a run of the expiry job, which ends the shares whose time it has reached.
  */
val askedStep = define { (a: Term[Asked], e: Term[Event]) =>
  e.on[Event.Wrote](w =>
    val own = (id: Term[BigInt]) => a.records.exists(x => x.id === id && x.tenant === w.by.tenant)
    val others = (id: Term[BigInt], to: Term[TenantId]) => a.grants.filter(g => !(g.record === id && g.to === to))
    w.change
      .on[Change.Add](r => when(r.tenant === w.by.tenant && !a.records.exists(x => x.id === r.id))(
        make[Asked](a.records :+ r, a.grants)).otherwise(a))
      .on[Change.ShareWith]((id, to, until) =>
        when(own(id))(make[Asked](a.records, others(id, to) :+ make[Grant](id, to, until))).otherwise(a))
      .on[Change.Unshare]((id, to) => when(own(id))(make[Asked](a.records, others(id, to))).otherwise(a)))
    .on[Event.Expired](now => make[Asked](a.records, a.grants.filter(g => g.until.noneOr(t => now < t)))) }

/** What a history asked, from nothing asked, each event in turn. */
val askedIn = define { (es: Term[List[Event]]) =>
  es.foldLeft(make[Asked](Nil: Term[List[CrmRecord]], Nil: Term[List[Grant]]))((a, e) => askedStep(a, e)) }

/** Whether, after a history, the record with that id is shared with the company at `now`: the last share of it with
  * that company still stands, and its time, if it has one, comes after `now`.
  */
val sharedIn = define { (es: Term[List[Event]], id: Term[BigInt], c: Term[TenantId], now: Term[BigInt]) =>
  askedIn(es).grants.exists(g => g.record === id && g.to === c && g.until.noneOr(t => now < t)) }

// ============================================================================
// What the root is expected to give
// ============================================================================

private val ann = Account("ann@acme", TenantId("acme"))
private val gil = Account("gil@globex", TenantId("globex"))
private val annContact = CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")
private val gilDeal = CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")
private val everything = Ask(Screen.Records, Search.Everything)

val sharedUntilATime = Node.claim("When Ann at Acme has added a contact, and Gil at Globex a deal he shared with " +
    "Acme until 100: at 50 Ann finds both, at 150 only her contact, and Gil never finds Ann's contact.")(
  (history === List(Event.Wrote(WriteCmd(ann, Change.Add(annContact))), Event.Wrote(WriteCmd(gil, Change.Add(gilDeal))),
    Event.Wrote(WriteCmd(gil, Change.ShareWith(2, TenantId("acme"), Some(100)))))) implies
    (((clock === 50) implies
        (results(ann, everything).contains(annContact) && results(ann, everything).contains(gilDeal))) &&
      ((clock === 150) implies
        (results(ann, everything).contains(annContact) && !results(ann, everything).contains(gilDeal))) &&
      !results(gil, everything).contains(annContact)))

val addedIsFound = Node.claim("A record a user adds to their company, under an id no record added before has, is " +
    "found from then on by each of their searches that asks for it.")(
  forall((u: Term[Account], r: Term[CrmRecord], pre: Term[List[Event]], post: Term[List[Event]], q: Term[Ask]) =>
    (history === pre ++ (make[Event.Wrote](make[WriteCmd](u, make[Change.Add](r))) :: post) &&
      r.tenant === u.tenant && !askedIn(pre).records.exists(x => x.id === r.id)) implies
      askMatches(q, r).implies(results(u, q).contains(r))))

val writesLeaveOthers = Node.claim("Nothing a user writes changes what anyone finds of another company's records: " +
    "after the write, a search finds of them what the history before it entitled it to.")(
  forall((es: Term[List[Event]], w: Term[WriteCmd], u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) =>
    (history === es :+ make[Event.Wrote](w) && r.tenant =!= w.by.tenant) implies
      (results(u, q).contains(r) === (askMatches(q, r) && askedIn(es).records.contains(r) &&
        (r.tenant === u.tenant || sharedIn(es, r.id, u.tenant, clock))))))

// ============================================================================
// The root: what a user's search finds, of what users asked
// ============================================================================

val sharedCrm = Node.claim("A user's search finds a record exactly when it asks for that record, a user of the " +
    "record's company added it, and it is of the user's company or currently shared with it by its own.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) => finds(u, q, r) ===
    (asksFor(q, r) && added(owner(r), r) && (owner(r) === companyOf(u) || sharedWith(r, companyOf(u))))))
  .refines(sharedUntilATime, addedIsFound, writesLeaveOthers)

// ============================================================================
// The purpose's words, each one equation
// ============================================================================

val companies = Node.claim("Companies are named by ids; a user is an account of one company.")(
  forall((a: Term[Account]) => companyOf(a) === a.tenant))
  .refines(sharedCrm)

val ownership = Node.claim("A record, a contact or a deal, belongs to the company stored on it.")(
  forall((r: Term[CrmRecord]) => owner(r) === r.tenant))
  .refines(sharedCrm)

val searches = Node.claim("A user searches by id, by kind or for everything, on the records screen or on the sales " +
    "screen, and finds what the search returns.")(
  forall((u: Term[Account], q: Term[Ask], r: Term[CrmRecord]) => finds(u, q, r) === results(u, q).contains(r)))
  .refines(sharedCrm)

val searchesAsk = Node.claim("A search on the records screen asks for what it matches, on the sales screen for the " +
    "deals it matches.")(
  forall((q: Term[Ask], r: Term[CrmRecord]) => asksFor(q, r) === askMatches(q, r)))
  .refines(sharedCrm)

val adding = Node.claim("A user of a company has added a record when a write of theirs in the CRM's history asked " +
    "to add it, of their company, under an id no record added before it had.")(
  forall((c: Term[TenantId], r: Term[CrmRecord]) =>
    added(c, r) === (r.tenant === c && askedIn(history).records.contains(r))))
  .refines(sharedCrm)

val sharing = Node.claim("A record is shared with a company now when the last share or unshare of it with that " +
    "company, by a user of its company once it was added, was a share, and neither the clock now nor a run of the " +
    "expiry job since has reached that share's time.")(
  forall((r: Term[CrmRecord], c: Term[TenantId]) => sharedWith(r, c) === sharedIn(history, r.id, c, clock)))
  .refines(sharedCrm)

val crmRun = Node.assumption("What the CRM holds now, its records, their shares and the shares' expiries, is what " +
    "its history led to: from empty, each write saved by the write side, the rows about its record replaced by " +
    "those it stored, and each run of the expiry job, in turn.")(
  held === runOf(history))
