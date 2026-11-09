package crm

import frflow.*

// ============================================================================
// What the CRM holds: exactly what users asked, by induction over its history
// ============================================================================

/** The CRM holds exactly the records its users added. */
private def heldAreAdded: Term[Boolean] =
  forall((r: Term[CrmRecord]) => held.records.contains(r) === askedIn(history).records.contains(r))

/** The CRM holds a share as current exactly when its users' requests share the record with that company now. */
private def heldSharesAreAsked: Term[Boolean] =
  forall((id: Term[BigInt], c: Term[TenantId]) => sharedNow(held, clock, id, c) === sharedIn(history, id, c, clock))

val storeMirrorsRequests = Node.claim("What the CRM holds is what its users asked.")(
  heldAreAdded &&
    heldSharesAreAsked)
  .refines(sharedCrm, addedIsFound, writesLeaveOthers)
  .assuming(keyedTables)

val recordsMirrorAdds = Node.claim("The CRM holds exactly the records its users added.")(heldAreAdded)
  .refines(storeMirrorsRequests)
  .assuming(keyedTables)

val sharesMirrorGrants = Node.claim("The CRM holds a share as current exactly when its users' requests share the " +
    "record with that company now.")(heldSharesAreAsked)
  .refines(storeMirrorsRequests)
  .assuming(keyedTables)

// What the history is of: what the database holds (a rule of its state, kept by the code that changes it).
val crmRun = Node.claim("What the CRM holds is what its history of events led to, from empty.")(
  always(databaseModel)(t => t.store === runOf(t.events)))
  .refines(recordsMirrorAdds, sharesMirrorGrants)
  .assuming(tablesModel, runsOneAtATime, tablesStartEmpty, keyedTables)

// ============================================================================
// Writing records: what a write does, and what it never does
// ============================================================================

val writesTakeEffect = Node.claim("A saved write does what its author asked, as far as their company may ask it.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => takesEffect(s, w, afterSave(s, w))))
  .refines(recordsMirrorAdds, sharesMirrorGrants)
  .assuming(keyedTables)

val writesOnlyAsAsked = Node.claim("A saved write changes nothing its author did not ask.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => onlyAsked(s, w, afterSave(s, w))))
  .refines(recordsMirrorAdds, sharesMirrorGrants)
  .assuming(keyedTables)

val recordsKept = Node.claim("No event removes a record the CRM holds.")(
  forall((s: Term[CrmStore], e: Term[Event]) => keepsRecords(s, stepOf(s, e))))
  .refines(recordsMirrorAdds, sharesMirrorGrants)
  .assuming(keyedTables)

// ============================================================================
// One write, and the write side that stores it
// ============================================================================

val writeContract = Node.claim("A write changes a store exactly as its author asked, as far as their company may " +
    "ask it.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) =>
    val written = write(s, w)
    keepsRecords(s, written) &&
      othersKept(s, w, written) &&
      takesEffect(s, w, written) &&
      onlyAsked(s, w, written)))
  .refines(writesTakeEffect, writesOnlyAsAsked, recordsKept)
  .assuming(keyedTables)

val writeKeepsRecords = Node.claim("A write keeps every record the store holds.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => keepsRecords(s, write(s, w))))
  .refines(writeContract)
  .assuming(keyedTables)

val writeKeepsOthers = Node.claim("A write leaves the records of other companies as they were.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => othersKept(s, w, write(s, w))))
  .refines(writeContract)
  .assuming(keyedTables)

val writeDoesAsked = Node.claim("A write does what its author asked, as far as their company may ask it.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => takesEffect(s, w, write(s, w))))
  .refines(writeContract)
  .assuming(keyedTables)

val writeOnlyAsked = Node.claim("A write changes nothing its author did not ask.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => onlyAsked(s, w, write(s, w))))
  .refines(writeContract)
  .assuming(keyedTables)

// ============================================================================
// The write side on the database
// ============================================================================

/** What the database holds after saving a write. */
private def afterSaving(w: Term[WriteCmd]): Term[Tables] = databaseModel.in(save(w).after)

val saveStores = Node.claim("Saving a write leaves the database holding, about the written record, what the write " +
    "leads to.")(
  forall((w: Term[WriteCmd]) => afterSaving(w).store === afterSave(held, w)))
  .assuming(runsOneAtATime, keyedTables)

val saveLogs = Node.claim("Saving a write appends it to the event log.")(
  forall((w: Term[WriteCmd]) => afterSaving(w).events === history :+ make[Event.Wrote](w)))
  .assuming(runsOneAtATime, keyedTables)

val saveReturns = Node.claim("Saving a write returns the rows the database then holds about its record.")(
  forall((w: Term[WriteCmd]) => save(w).result === aboutRecord(afterSave(held, w), about(w))))
  .assuming(runsOneAtATime, keyedTables)

/** The write side: the write applied to the store the database holds, the rows about its record stored, the write
  * logged; the rows returned.
  */
val saved = program { (w: Term[WriteCmd]) =>
  for
    s <- load
    t  = applyWrite(s, w)
    _ <- storeAbout(about(w), t)
    _ <- logEvent(make[Event.Wrote](w))
  yield aboutRecord(t, about(w)) }

val writeSideWiring = Node.design("The write side runs its proven program on SQLite.")(
  "src/main/scala/crm/WriteSide.scala", "src/main/scala/crm/EventLog.scala")
  .refines(saveStores, saveLogs, saveReturns)

// ============================================================================
// The tables hold one row per key (owner §40): a rule below what the CRM holds. keyedTables trusts it of the stores
// from outside (2.6); this claim is the owner's, proven where the CRM's code makes a store (made_, cover_).
// ============================================================================

val oneRowPerKey = Node.claim("Every store the CRM makes holds one row per key.")(
  always[CrmStore](s => onePerKey(s)))
  .refines(recordsMirrorAdds, sharesMirrorGrants)
  .assuming(keyedTables, tablesModel, runsOneAtATime, tablesStartEmpty)
