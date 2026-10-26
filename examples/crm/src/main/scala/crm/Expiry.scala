package crm

import frflow.*

// ============================================================================
// Expiring shares: a job clears the shares whose time has come
// ============================================================================

val sharesExpire = Node.contract(expire)("SharesExpire",
  "A run of the expiry job at a time removes exactly the shares given until then or earlier, with their times, and keeps every record and every other share's time.",
  why = "The idea lets a company share a record until a given time. A search already ignores a share past its time (Sharing): the job clears such shares from the tables, and it touches nothing else, so it never ends a share early nor keeps one past its time. Keeping the records is what keeps them found (RecordsKept).",
  idea = "Expiring shares"
)((s, now, t) => endsDueAt(s, now, t))
  .refines(storeMirrorsRequests, recordsKept)
  .examples()(
    allows(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("initech"))), Nil), "Globex's share ended at 100; Initech's stays"),
    allows(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), 50,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), "before 100 nothing ends"),
    forbids(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a share that has not ended is never removed"),
    forbids(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(Nil, Nil, Nil), "a run never removes a record"))
  .exempt(noCrossTenantRead, "the store it returns goes to storage, never to a reader")

/** A run: the shares that have not ended, and the expiries of those. */
val expireCode = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  CrmStore(s.records, s.shares.filter(sh => !ended(sh, s, now)), s.expiries.filter(e => !ended(Share(e.record, e.to), s, now)))
}

// ============================================================================
// The job on the database: a flow, proven from the database's model
// ============================================================================

val runExpiry = Param[BigInt => Flow[CrmStore]]("runExpiry",
  "a run of the expiry job at a time (in seconds), on the database: the store it computes; the database holds it after")

/** The ids of the records a store holds anything about: its records, their shares and their expiries. */
val idsIn = define { (s: Term[CrmStore]) => s.records.map(r => r.id) ++ s.shares.map(sh => sh.record) ++ s.expiries.map(e => e.record) }

/** The records whose rows differ between two stores: what storing the second over the first must store. */
val changedIds = define { (s: Term[CrmStore], t: Term[CrmStore]) =>
  (idsIn(s) ++ idsIn(t)).filter(id => aboutRecord(s, id) =!= aboutRecord(t, id))
}

/** Whether two stores hold the same rows about every record, in the same order for each. */
val sameRows = define { (a: Term[CrmStore], b: Term[CrmStore]) =>
  (idsIn(a) ++ idsIn(b)).forall(id => aboutRecord(a, id) === aboutRecord(b, id))
}

private val acmeDeal = CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")
private val globexUntil100 = CrmStore(List(acmeDeal), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100)))
private val initechOnly = CrmStore(List(acmeDeal), List(Share(1, TenantId("initech"))), Nil)
// Two records out of the database's order (it returns rows sorted by record): the model and SQLite must agree on them.
private val acmeContact = CrmRecord(2, TenantId("acme"), Kind.Contact, "Acme contact")
private val twoUnsorted = CrmStore(List(acmeContact, acmeDeal), List(Share(2, TenantId("globex")), Share(1, TenantId("initech"))),
  List(Expiry(2, TenantId("globex"), 100)))
private val twoExpired = CrmStore(List(acmeContact, acmeDeal), List(Share(1, TenantId("initech"))), Nil)
private val twoStored = CrmStore(List(acmeDeal, acmeContact), List(Share(1, TenantId("initech"))), Nil)
private val earlier = List(Event.Wrote(WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(acmeDeal))))

val expiryJob = Node.contract(runExpiry)("ExpiryJob",
  "A run of the expiry job at a time leaves the database holding, about each record, what SharesExpire's run on what it held gives, logs the run at the end of the event log, and returns that store.",
  why = "The job is how SharesExpire's operation reaches the database: it loads what the database holds, runs the operation on it, stores the rows of each record whose rows changed, and logs the run, which is what makes the event log the history CrmRun replays. Proven of the code from the database's model (TablesModel), it is no longer only reviewed wiring.",
  idea = "Expiring shares"
)((now, result, before, after) =>
  sameRows(after(DatabaseModel).store, expire(before(DatabaseModel).store, now)) &&
    after(DatabaseModel).events === before(DatabaseModel).events ++ List(Event[Event.Expired](now)) &&
    result === expire(before(DatabaseModel).store, now))
  .examples()(
    allows(BigInt(150), World(DatabaseModel -> Tables(globexUntil100, earlier)), initechOnly,
      World(DatabaseModel -> Tables(initechOnly, earlier :+ Event.Expired(150))), "Globex's share ended at 100: the database drops it, and the run is logged"),
    allows(BigInt(150), World(DatabaseModel -> Tables(twoUnsorted, earlier)), twoExpired,
      World(DatabaseModel -> Tables(twoStored, earlier :+ Event.Expired(150))), "two records: the contact's share with Globex ended; the database stores the contact's rows again"),
    allows(BigInt(50), World(DatabaseModel -> Tables(globexUntil100, earlier)), globexUntil100,
      World(DatabaseModel -> Tables(globexUntil100, earlier :+ Event.Expired(50))), "before 100 nothing ends, and the run is still logged"),
    forbids(BigInt(150), World(DatabaseModel -> Tables(globexUntil100, earlier)), initechOnly,
      World(DatabaseModel -> Tables(globexUntil100, earlier :+ Event.Expired(150))), "a run that stores nothing leaves an ended share in the database"),
    forbids(BigInt(150), World(DatabaseModel -> Tables(globexUntil100, earlier)), initechOnly,
      World(DatabaseModel -> Tables(initechOnly, earlier)), "a run is never left out of the event log"))
  .exempt(noCrossTenantRead, "it hands the new store to the database and returns nothing to a reader")

val expiryJobWiring = Node.design(
  "ExpiryJobWiring",
  "The expiry job runs every minute, holding the database's lock during a run so no write interleaves with it; its code is the flow ExpiryJob is proven of, run on SQLite.",
  why = "What a run does is proven (ExpiryJob); when it runs, and that no write interleaves with it, is decided here and reviewed: the model assumes a run has the database to itself.",
  idea = "Expiring shares"
)("src/main/scala/crm/Job.scala")
  .refines(expiryJob)
  .exempt(noCrossTenantRead, "it hands the new store to storage and returns nothing to a reader")
