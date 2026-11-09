package crm

import frflow.*

/** Whether a record is one a search asks for. */
val matches = define { (q: Term[Search], r: Term[CrmRecord]) =>
  q.on[Search.ById](id => r.id === id)
    .on[Search.OfKind](k => r.kind === k)
    .on[Search.Everything.type](True) }

/** Whether a share has ended by `now`, by the store's expiries. */
val ended = define { (sh: Term[Share], s: Term[CrmStore], now: Term[BigInt]) =>
  s.expiries.exists(e => e.record === sh.record && e.to === sh.to && e.until <= now) }

/** Whether the store holds the share of the record with the company, and it has not ended by `now`. */
val sharedNow = define { (held: Term[CrmStore], now: Term[BigInt], id: Term[BigInt], c: Term[TenantId]) =>
  held.shares.contains(make[Share](id, c)) && !ended(make[Share](id, c), held, now) }

/** Whether a reader may see a record, by a store at a time: it is their company's, or shared with it then. */
val mayRead = define { (held: Term[CrmStore], now: Term[BigInt], reader: Term[Account], r: Term[CrmRecord]) =>
  r.tenant === reader.tenant || sharedNow(held, now, r.id, reader.tenant) }

/** Whether a record is one a search on a screen asks for: the sales screen asks for deals only. */
val askMatches = define { (q: Term[Ask], r: Term[CrmRecord]) =>
  q.screen.on[Screen.Records.type](matches(q.search, r))
    .on[Screen.Sales.type](r.kind === (Kind.Deal: Kind) && matches(q.search, r)) }

/** What a search on a screen returns, of what each screen returns: the records screen's, or the sales screen's. */
val onScreen = define { (q: Term[Ask], records: Term[List[CrmRecord]], sales: Term[List[CrmRecord]]) =>
  q.screen.on[Screen.Records.type](records).on[Screen.Sales.type](sales) }

/** What a user's search on a screen returns, run now: the records screen's run, or the sales screen's. */
def results(u: Term[Account], q: Term[Ask]): Term[List[CrmRecord]] =
  onScreen(q, read(u, q.search).result, deals(u, q.search).result)

/** Whether a reader may see a record now: what the CRM holds now, at the clock's time. */
def mayReadNow(reader: Term[Account], r: Term[CrmRecord]): Term[Boolean] = mayRead(held, clock, reader, r)

/** The shares of a store that have not ended by `now`. */
val liveShares = define { (s: Term[CrmStore], now: Term[BigInt]) => s.shares.filter(sh => !ended(sh, s, now)) }

/** The expiries of a store whose shares have not ended by `now`. */
val liveExpiries = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  s.expiries.filter(e => !ended(make[Share](e.record, e.to), s, now)) }

/** Whether two stores hold the same records. */
val sameRecords = define { (s: Term[CrmStore], t: Term[CrmStore]) => t.records === s.records }

/** Whether the second store's shares are exactly the first's that have not ended by `now`. */
val onlyLiveShares = define { (s: Term[CrmStore], now: Term[BigInt], t: Term[CrmStore]) =>
  t.shares === liveShares(s, now) }

/** Whether the second store's times are exactly the first's for the shares that have not ended by `now`. */
val onlyLiveTimes = define { (s: Term[CrmStore], now: Term[BigInt], t: Term[CrmStore]) =>
  t.expiries === liveExpiries(s, now) }

/** A run of the expiry job (the code of `expire`): the same records, the shares that have not ended, and their
  * times.
  */
val expireCode = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  make[CrmStore](s.records, liveShares(s, now), liveExpiries(s, now)) }

/** The ids of the records a store holds anything about: its records, their shares and their expiries. */
val idsIn = define { (s: Term[CrmStore]) =>
  s.records.map(r => r.id) ++ s.shares.map(sh => sh.record) ++ s.expiries.map(e => e.record) }

/** The first store with the rows of each record the second holds differently stored again from the second. */
val storedAgain = define { (s: Term[CrmStore], t: Term[CrmStore]) =>
  (idsIn(s) ++ idsIn(t)).foldLeft(s)((x, id) =>
    when(aboutRecord(s, id) =!= aboutRecord(t, id))(replaceAbout(x, id, aboutRecord(t, id))).otherwise(x)) }

/** What the database holds after a run of the expiry job at `now`: the job's store stored again where it differs. */
val jobDone = define { (s: Term[CrmStore], now: Term[BigInt]) => storedAgain(s, expireCode(s, now)) }

/** One event: a write, saved by the write side, or a run of the expiry job as the database holds it after
  * (`jobDone`).
  */
val stepOf = define { (s: Term[CrmStore], e: Term[Event]) =>
  e.on[Event.Wrote](w => afterSave(s, w)).on[Event.Expired](now => jobDone(s, now)) }

/** The store a history of events leads to, from the empty store the CRM starts with. */
val runOf = define { (es: Term[List[Event]]) =>
  es.foldLeft(make[CrmStore](Nil: Term[List[CrmRecord]], Nil: Term[List[Share]], Nil: Term[List[Expiry]]))(
    (s, e) => stepOf(s, e)) }

/** Whether a store holds one row per key: a record by its id, a share and an expiry by record and company. */
val onePerKey = define { (s: Term[CrmStore]) =>
  s.records.pairwise((a, b) => a.id =!= b.id) && s.shares.pairwise((a, b) => a =!= b) &&
    s.expiries.pairwise((a, b) => !(a.record === b.record && a.to === b.to)) }
