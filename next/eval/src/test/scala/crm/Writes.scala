package crm

import frflow.*

// ============================================================================
// What the CRM holds: exactly what users asked, by induction over its history
// ============================================================================

val storeMirrorsRequests = Node.claim("The CRM holds exactly the records its users added, and holds a share of a " +
    "record as current exactly when the record's company shared it so.")(
  forall((r: Term[CrmRecord]) => held.records.contains(r) === askedIn(history).records.contains(r)) &&
    forall((id: Term[BigInt], c: Term[TenantId]) => sharedNow(held, clock, id, c) === sharedIn(history, id, c, clock)))
  .refines(sharedCrm, addedIsFound, writesLeaveOthers)
  .assuming(keyedTables)

// What the history is of: what the database holds (a rule of its state, kept by the code that changes it).
val crmRun = Node.claim("What the CRM holds now, its records, their shares and the shares' expiries, is what " +
    "its history led to: from empty, each write saved by the write side, the rows about its record replaced by " +
    "those it stored, and each run of the expiry job, in turn.")(
  always(databaseModel)(t => t.store === runOf(t.events)))
  .refines(storeMirrorsRequests)
  .assuming(tablesModel, runsOneAtATime, tablesStartEmpty, keyedTables)

// ============================================================================
// Writing records: what a write does, and what it never does
// ============================================================================

val writesTakeEffect = Node.claim("A user's write about their company's record does what they asked: it adds the " +
    "record, shares it (until a time, or for good), or unshares it.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => takesEffect(s, w, afterSave(s, w))))
  .refines(storeMirrorsRequests)
  .assuming(keyedTables)

val writesOnlyAsAsked = Node.claim("A write changes nothing its author did not ask of their company's records: it " +
    "adds no other record, and changes no other share or share's time.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => onlyAsked(s, w, afterSave(s, w))))
  .refines(storeMirrorsRequests)
  .assuming(keyedTables)

val recordsKept = Node.claim("No write and no run of the expiry job removes a record: after each, the CRM holds " +
    "every record it held before.")(
  forall((s: Term[CrmStore], e: Term[Event]) => s.records.forall(r => stepOf(s, e).records.contains(r))))
  .refines(storeMirrorsRequests)
  .assuming(keyedTables)

// ============================================================================
// One write, and the write side that stores it
// ============================================================================

val writeContract = Node.claim("A write keeps every record, leaves the records of other companies as they were, " +
    "does what its author asked of their company's records, and changes nothing else.")(
  forall((s: Term[CrmStore], w: Term[WriteCmd]) => s.records.forall(r => write(s, w).records.contains(r)) &&
    write(s, w).records.filter(r => r.tenant =!= w.by.tenant) === s.records.filter(r => r.tenant =!= w.by.tenant) &&
    takesEffect(s, w, write(s, w)) && onlyAsked(s, w, write(s, w))))
  .refines(writesTakeEffect, writesOnlyAsAsked, recordsKept)
  .assuming(keyedTables)

val saveWrite = Node.claim("Saving a write leaves the database holding, about the written record, what the store the " +
    "write leads to holds about it, logs the write at the end of the event log, and returns those rows.")(
  forall((w: Term[WriteCmd]) =>
    databaseModel.in(save(w).after) === make[Tables](afterSave(held, w), history :+ make[Event.Wrote](w)) &&
      save(w).result === aboutRecord(afterSave(held, w), about(w))))
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

val writeSideWiring = Node.design("The write side saves each write on the store loaded from the database, one " +
    "write at a time, and logs it in the event log.")(
  "src/main/scala/crm/WriteSide.scala", "src/main/scala/crm/EventLog.scala")
  .refines(saveWrite)

// ============================================================================
// The tables hold one row per key (owner §40): a rule below what the CRM holds
// ============================================================================

val oneRowPerKey = Node.claim("Every store the CRM makes holds one row per key, as the database's tables do: a " +
    "record by its id, a share and an expiry by record and company.")(
  always[CrmStore](s => onePerKey(s)))
  .refines(storeMirrorsRequests)
  .assuming(keyedTables, tablesModel, runsOneAtATime, tablesStartEmpty)
