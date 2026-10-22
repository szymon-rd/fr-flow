package crm

import frflow.*

// ============================================================================
// Writing records: what a write does, and what it never does
// ============================================================================

val writesTakeEffect = Node.claim("WritesTakeEffect",
  "A user's write about their company's record does what they asked: it adds the record, shares it (until a time, or for good), or unshares it.",
  why = "What the idea says users can do with their company's records. It is about what the database holds after the write, not only what the write computes: a write that is not stored has not happened.",
  idea = "Writing records"
)(forall((s: CrmStore, w: WriteCmd) => takesEffect(s, w, afterSave(s, w))))
  .under(sharedCrm, addedAreFound)

val writesInCompany = Node.claim("WritesInCompany",
  "In every store the CRM reaches, a write leaves every other company's records, and whom they are shared with until when, as they were.",
  why = "No write may change another company's records, nor share or unshare them: that would change what other companies see. A share names a record by its id, so this holds only where ids are unique: in the stores the CRM reaches (StoreConsistent).",
  idea = "Writing records"
)(forall((es: List[Event], w: WriteCmd) => forall((c: TenantId) =>
  (c != w.by.tenant) ==> holdsAlike(runOf(es), afterSave(runOf(es), w), c))))
  .under(sharedCrm)

val storeConsistent = Node.claim("StoreConsistent",
  "No two records have one id in any store the CRM reaches, by writes and by runs of the expiry job.",
  why = "A share names a record by its id: with two records of one id, sharing one would share the other, across companies. Every write and every run of the job keeps ids unique, so every store reached from the empty one has them unique (by induction over the events). The job is an event like the writes: it is covered too.",
  idea = "Writing records"
)(forall((es: List[Event]) => idsUnique(runOf(es))))
  .under(writesInCompany)

val recordsKept = Node.claim("RecordsKept",
  "No write and no run of the expiry job removes a record: after each, the CRM holds every record it held before.",
  why = "Editing or removing records is not modelled, so a record once stored stays: a write changes shares or adds a record, and the job ends shares only. This is what makes an added record found from then on, not only right after its write.",
  idea = "Writing records"
)(forall((s: CrmStore, e: Event) => s.records.forall(r => stepOf(s, e).records.contains(r))))
  .under(addedAreFound)

// ============================================================================
// Contracts: one write, and the write side that stores it
// ============================================================================

val writeContract = Node.contract(write)("WriteContract",
  "A write keeps every record, leaves the records of other companies as they were, does what its author asked of their company's records, and on a store with unique ids keeps them unique and leaves other companies' shares and expiries as they were.",
  why = "The writing rules, stated for one write on a store: what the user asked takes effect, no record is lost, and nothing of another company's changes. A write the author's company may not make changes nothing.",
  idea = "Writing records"
)((s, w, t) => s.records.forall(r => t.records.contains(r)) &&
  t.records.filter(r => r.tenant != w.by.tenant) == s.records.filter(r => r.tenant != w.by.tenant) && takesEffect(s, w, t) &&
  (idsUnique(s) ==> (idsUnique(t) && s.records.forall(r => (r.tenant != w.by.tenant) ==> rowsAlike(s, t, r.id)))))
  .under(writesTakeEffect, writesInCompany, storeConsistent, recordsKept)
  // Per call, in time linear in the store: the write took effect, and other companies' records are as they were.
  // The rest (no record lost, unique ids, other companies' shares) is proven of the code, and would read every pair of rows.
  .checkedBy((s, w, t) => takesEffect(s, w, t) && t.records.filter(r => r.tenant != w.by.tenant) == s.records.filter(r => r.tenant != w.by.tenant))
  .examples()(
    expect(CrmStore(Nil, Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil),
      "Ann adds a contact of Acme's"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"), None)),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(1, TenantId("globex"))), Nil), "Ann shares Acme's contact with Globex"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"), Some(100))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), "Ann shares it with Globex until 100"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(2, TenantId("acme"), None)),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(2, TenantId("acme"))), Nil), "Ann cannot share Globex's deal with herself"),
    reject(CrmStore(List(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))), CrmStore(Nil, Nil, Nil),
      "a write never removes another company's record"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"), CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a record with a taken id is never added beside it"))
  .exempt(noCrossTenantRead, "the store a write returns goes to the write side, never to a reader: reads go through ReadContract")

/** A write: the change, when its author's company may make it; otherwise nothing changes. */
val applyWrite = define { (s: CrmStore, w: WriteCmd) =>
  w.change match
    case Change.Add(r) =>
      if r.tenant == w.by.tenant && !s.records.exists(x => x.id == r.id) then CrmStore(s.records ++ List(r), s.shares, s.expiries) else s
    case Change.ShareWith(id, to, until) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
        CrmStore(s.records, s.shares.filter(sh => sh != Share(id, to)) ++ List(Share(id, to)),
          s.expiries.filter(e => !(e.record == id && e.to == to)) ++ (until match
            case Some(u) => List(Expiry(id, to, u))
            case None    => Nil))
      else s
    case Change.Unshare(id, to) =>
      if s.records.exists(x => x.id == id && x.tenant == w.by.tenant) then
        CrmStore(s.records, s.shares.filter(sh => sh != Share(id, to)), s.expiries.filter(e => !(e.record == id && e.to == to)))
      else s
}

val saveWrite = Node.contract(save)("SaveWrite",
  "Saving a write stores, and returns as read back, what the store the write leads to holds about the written record.",
  why = "A write changes only its own record's rows, so storing those rows stores the write, whatever the size of the store: the database then holds what CrmRun says. The rows are read back, so a write the database dropped or changed is seen on the call.",
  idea = "Writing records"
)((s, w, back) => back == aboutRecord(write(s, w), about(w)))
  .under(writesTakeEffect, writesInCompany, storeConsistent, recordsKept)
  // Per call: the rows read back are about the written record. That they are the write's is proven of the
  // code, from StoreEdits; checking it would run the write twice.
  .checkedBy((s, w, back) => back.records.forall(r => r.id == about(w)) && back.shares.forall(sh => sh.record == about(w)) &&
    back.expiries.forall(e => e.record == about(w)))
  .examples(database.bind(Db.of(Nil)))(
    expect(CrmStore(List(CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(2, TenantId("acme"))), Nil),
      WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil), "Ann's new contact is stored, and only its rows"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), Nil, Nil),
      WriteCmd(Account("ann@acme", TenantId("acme")), Change.ShareWith(1, TenantId("globex"), Some(100))),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))),
      "sharing until 100 stores the record's share and its expiry"),
    reject(CrmStore(Nil, Nil, Nil), WriteCmd(Account("ann@acme", TenantId("acme")), Change.Add(CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact"))),
      CrmStore(Nil, Nil, Nil), "a write the database dropped is seen"))
  .exempt(noCrossTenantRead, "it returns the rows it stored to the write side, never to a reader")

/** The write side: apply the write, store the rows about its record, return them as read back. */
val saved = define { (s: CrmStore, w: WriteCmd) => storeRows(about(w), write(s, w)) }

// ============================================================================
// Port: the database storing the rows about one record
// ============================================================================

/** What the database is trusted to do with a write: store what a store holds about one record. */
val storeEdits = Node.assumption(storeRows)("StoreEdits",
  "Storing what a store holds about one record replaces what the database holds about it, and nothing else; read back, the rows about it are what the store holds about it.",
  why = "The database is outside the proofs: the write side is proven from this promise. The rows are read back after storing, and checked: a write the database dropped or changed is seen on the call. That it changes nothing else is trusted (CrmRun)."
)((id, t, back) => back == aboutRecord(t, id))
  .examples(database.bind(Db.of(Nil, Nil)))(
    expect(BigInt(1), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal"), CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")), List(Share(1, TenantId("globex"))), Nil),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), Nil), "the record and its share, not the other record"),
    expect(BigInt(3), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), CrmStore(Nil, Nil, Nil), "nothing is held about record 3"),
    reject(BigInt(1), CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), Nil),
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a share the database dropped is seen"))

/** The rows about a record, as the port promises them: what the SQL is checked against. */
val storedAbout = define { (id: BigInt, t: CrmStore) => aboutRecord(t, id) }

/** The production wiring of writes, owned as a design decision: changes to it are reviewed. */
val writeSideWiring = Node.design(
  "WriteSideWiring",
  "The write side saves each write through service, on the store loaded from the database, one write at a time, and logs it in the event log.",
  why = "Every write must go through service, which checks what each step returns; one write at a time, so each starts from the store the last one left. The event log is the CRM's history (CrmRun): the write side and the expiry job each log their event after storing it. Keeping the wiring in governed files makes a change to it visible."
)("src/main/scala/crm/WriteSide.scala", "src/main/scala/crm/EventLog.scala")
  .under(saveWrite)
  .exempt(noCrossTenantRead, "the write side hands rows to storage and returns them to its caller, never records to a reader")
