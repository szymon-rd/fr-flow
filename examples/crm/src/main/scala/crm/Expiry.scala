package crm

import frflow.*

// ============================================================================
// Expiring shares: a share given until a time ends then, by a job
// ============================================================================

val sharesExpire = Node.contract(expire)("SharesExpire",
  "A run of the expiry job at a time ends exactly the shares given until then or earlier, and keeps every record.",
  why = "The idea lets a company share a record until a given time; the job is what ends such shares, and it touches nothing else. Keeping the records is also what keeps their ids unique when the job runs (StoreConsistent).",
  idea = "Expiring shares"
)((s, now, t) => endsDueAt(s, now, t))
  .under(sharedCrm, storeConsistent)
  .examples()(
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("initech"))), Nil), "Globex's share ended at 100; Initech's stays"),
    expect(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), 50,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), "before 100 nothing ends"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex")), Share(1, TenantId("initech"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), Nil, Nil), "a share that has not ended is never removed"),
    reject(CrmStore(List(CrmRecord(1, TenantId("acme"), Kind.Deal, "Acme deal")), List(Share(1, TenantId("globex"))), List(Expiry(1, TenantId("globex"), 100))), 150,
      CrmStore(Nil, Nil, Nil), "a run never removes a record"))
  .exempt(noCrossTenantRead, "the store it returns goes to storage, never to a reader")

/** A run: the shares that have not ended, and the expiries of those. */
val expireCode = define { (s: CrmStore, now: BigInt) =>
  CrmStore(s.records, s.shares.filter(sh => !ended(sh, s, now)), s.expiries.filter(e => !ended(Share(e.record, e.to), s, now)))
}

/** The job's wiring, owned as a design decision. */
val expiryJobWiring = Node.design(
  "ExpiryJobWiring",
  "The expiry job runs every minute through service, on the stored records, shares and expiries, and stores the rows of each record it changed through StoreEdits.",
  why = "Every change to the store goes through a proven contract and a checked port; keeping the job's wiring in one governed file makes a change to it visible.",
  idea = "Expiring shares"
)("src/main/scala/crm/Job.scala")
  .under(sharesExpire)
  .exempt(noCrossTenantRead, "it hands the new store to storage and returns nothing to a reader")
