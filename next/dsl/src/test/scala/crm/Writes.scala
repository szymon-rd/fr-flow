package crm

import examples.Folds.*
import frflow.*

// ============================================================================
// What the CRM holds: exactly what users asked, by induction over its history
// ============================================================================

val storeMirrorsRequests = Node.claim("The CRM holds exactly the records its users added, and holds a share of a " +
    "record as current exactly when the record's company shared it so.")(
  forall((r: Term[CrmRecord]) => held.records.contains(r) === askedIn(history).records.contains(r)) &&
    forall((id: Term[BigInt], c: Term[TenantId]) => sharedNow(id, c) === sharedIn(history, id, c, clock)))
  .refines(sharedCrm)
  .assuming(crmRun)

// ============================================================================
// Writing records: what a write does, and what it never does
// ============================================================================

val writesTakeEffect = Node.claim("A user's write about their company's record does what they asked: it adds the " +
    "record, shares it (until a time, or for good), or unshares it.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => takesEffect(s, w, afterSave(s, w))))
  .refines(storeMirrorsRequests)

val writesOnlyAsAsked = Node.claim("A write changes nothing its author did not ask of their company's records: it " +
    "adds no other record, and changes no other share or share's time.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => onlyAsked(s, w, afterSave(s, w))))
  .refines(storeMirrorsRequests)

val recordsKept = Node.claim("No write and no run of the expiry job removes a record: after each, the CRM holds " +
    "every record it held before.")(
  forall((s: Term[CrmStore], e: Term[Event]) => s.records.forall(r => stepOf(s, e).records.contains(r))))
  .refines(storeMirrorsRequests)

// ============================================================================
// One write, and the write side that stores it
// ============================================================================

val writeContract = Node.claim("A write keeps every record, leaves the records of other companies as they were, " +
    "does what its author asked of their company's records, and changes nothing else.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => s.records.forall(r => write(s, w).records.contains(r)) &&
    write(s, w).records.filter(r => r.tenant =!= w.by.tenant) === s.records.filter(r => r.tenant =!= w.by.tenant) &&
    takesEffect(s, w, write(s, w)) && onlyAsked(s, w, write(s, w))))
  .refines(writesTakeEffect, writesOnlyAsAsked, recordsKept)

/** A write: the change, when its author's company may make it; otherwise nothing changes. */
val applyWrite = define { (s: Term[CrmStore], w: Term[WriteCmd]) =>
  val othersOf = (id: Term[BigInt], to: Term[TenantId]) => s.expiries.filter(e => !(e.record === id && e.to === to))
  w.change
    .on[Change.Add](r => when(r.tenant === w.by.tenant && !s.records.exists(x => x.id === r.id))(
      make[CrmStore](s.records :+ r, s.shares, s.expiries)).otherwise(s))
    .on[Change.ShareWith]((id, to, until) => when(ownRecord(s, w, id))(make[CrmStore](s.records,
      s.shares.filter(sh => sh =!= make[Share](id, to)) :+ make[Share](id, to),
      othersOf(id, to) ++ until.fold(Nil: Term[List[Expiry]])(u => make[Expiry](id, to, u) :: (Nil: Term[List[Expiry]])))).otherwise(s))
    .on[Change.Unshare]((id, to) => when(ownRecord(s, w, id))(make[CrmStore](s.records,
      s.shares.filter(sh => sh =!= make[Share](id, to)), othersOf(id, to))).otherwise(s)) }

val saveWrite = Node.claim("Saving a write stores, and returns as read back, what the store the write leads to " +
    "holds about the written record.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => save(s, w) === aboutRecord(write(s, w), about(w))))
  .refines(writesTakeEffect, writesOnlyAsAsked, recordsKept)

/** The write side: apply the write, store the rows about its record, return them as read back. */
val saved = define { (s: Term[CrmStore], w: Term[WriteCmd]) => storeRows(about(w), write(s, w)) }

// ============================================================================
// The database storing the rows about one record
// ============================================================================

val storeEdits = Node.assumption("Storing what a store holds about one record replaces what the database holds " +
    "about it, and nothing else; read back, the rows about it are what the store holds about it.")(
  forall((id: Term[BigInt], t: Term[CrmStore]) => storeRows(id, t) === aboutRecord(t, id)))

val writeSideWiring = Node.design("The write side saves each write on the store loaded from the database, one " +
    "write at a time, and logs it in the event log.")(
  "src/main/scala/crm/WriteSide.scala", "src/main/scala/crm/EventLog.scala")
  .refines(saveWrite)
