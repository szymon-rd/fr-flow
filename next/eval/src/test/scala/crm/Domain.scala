package crm

import frflow.*

/** Whether a record is one a search asks for. */
val matches = define { (q: Term[Search], r: Term[CrmRecord]) =>
  q.on[Search.ById](id => r.id === id)
    .on[Search.OfKind](k => r.kind === k)
    .on[Search.Everything.type](True) }

/** Whether a store holds a share of the record with that id with the company, and the share's time, if it was given
  * until one, has not come by `now` (what the CRM holds now, `held`, at the clock's time).
  */
val sharedNow = define { (held: Term[CrmStore], now: Term[BigInt], id: Term[BigInt], c: Term[TenantId]) =>
  held.shares.contains(make[Share](id, c)) &&
    !held.expiries.exists(e => e.record === id && e.to === c && e.until <= now) }

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

/** The record a write is about. */
val about = define { (w: Term[WriteCmd]) =>
  w.change.on[Change.Add](r => r.id).on[Change.ShareWith]((id, _, _) => id).on[Change.Unshare]((id, _) => id) }

/** What a store holds about one record: the record (by its id), its shares and their expiries. */
val aboutRecord = define { (s: Term[CrmStore], id: Term[BigInt]) =>
  make[CrmStore](s.records.filter(r => r.id === id), s.shares.filter(sh => sh.record === id),
    s.expiries.filter(e => e.record === id)) }

/** A store with what it holds about one record replaced by the given rows. */
val replaceAbout = define { (s: Term[CrmStore], id: Term[BigInt], rows: Term[CrmStore]) =>
  make[CrmStore](s.records.filter(r => r.id =!= id) ++ rows.records,
    s.shares.filter(sh => sh.record =!= id) ++ rows.shares, s.expiries.filter(e => e.record =!= id) ++ rows.expiries) }

/** Whether the store holds a record of that id of the write's author's company. */
val ownRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt]) =>
  s.records.exists(x => x.id === id && x.tenant === w.by.tenant) }

/** A write (the code of `write`): the change, when its author's company may make it; otherwise nothing changes. */
val applyWrite = define { (s: Term[CrmStore], w: Term[WriteCmd]) =>
  val noExpiries: Term[List[Expiry]] = Nil
  val othersOf = (id: Term[BigInt], to: Term[TenantId]) => s.expiries.filter(e => !(e.record === id && e.to === to))
  w.change
    .on[Change.Add](r => when(r.tenant === w.by.tenant && !s.records.exists(x => x.id === r.id))(
      make[CrmStore](s.records :+ r, s.shares, s.expiries)).otherwise(s))
    .on[Change.ShareWith]((id, to, until) => when(ownRecord(s, w, id))(make[CrmStore](s.records,
      s.shares.filter(sh => sh =!= make[Share](id, to)) :+ make[Share](id, to),
      othersOf(id, to) ++ until.fold(noExpiries)(u => make[Expiry](id, to, u) :: noExpiries))).otherwise(s))
    .on[Change.Unshare]((id, to) => when(ownRecord(s, w, id))(make[CrmStore](s.records,
      s.shares.filter(sh => sh =!= make[Share](id, to)), othersOf(id, to))).otherwise(s)) }

/** What the database holds after the write side saves a write: what it held, with the rows about the written record
  * replaced by those the write's code (`applyWrite`, the code of `write`) leads to about it, as its `storeAbout` holds
  * them: a rule of the database reads values, not a Definition left open.
  */
val afterSave = define { (s: Term[CrmStore], w: Term[WriteCmd]) =>
  replaceAbout(s, about(w), aboutRecord(applyWrite(s, w), about(w))) }

/** What a write asks, as far as its author's company may ask it: an Add of a record of their company with a fresh id
  * stores it; a share of a record of their company is made, until the time given (its only time) or for good (with
  * no time); an unshare removes it.
  */
val takesEffect = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  w.change
    .on[Change.Add](r =>
      (r.tenant === w.by.tenant && !s.records.exists(x => x.id === r.id)) implies t.records.contains(r))
    .on[Change.ShareWith]((id, to, until) => ownRecord(s, w, id) implies (t.shares.contains(make[Share](id, to)) &&
      until.fold(!t.expiries.exists(e => e.record === id && e.to === to))(u =>
        t.expiries.contains(make[Expiry](id, to, u)) &&
          t.expiries.forall(e => (e.record === id && e.to === to) implies (e.until === u)))))
    .on[Change.Unshare]((id, to) => ownRecord(s, w, id) implies !t.shares.contains(make[Share](id, to))) }

/** Whether a write adds the record: it asks to add it, of its author's company, under an id no record the store
  * holds has.
  */
val addsRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], r: Term[CrmRecord]) =>
  w.change
    .on[Change.Add](x => x === r && r.tenant === w.by.tenant && !s.records.exists(y => y.id === r.id))
    .on[Change.ShareWith]((_, _, _) => False)
    .on[Change.Unshare]((_, _) => False) }

/** Whether a write changes the share of the record with that id with the company: it shares or unshares it, and the
  * store holds a record of that id of its author's company.
  */
val changesShare = define { (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], c: Term[TenantId]) =>
  w.change
    .on[Change.Add](_ => False)
    .on[Change.ShareWith]((i, to, _) => i === id && to === c && ownRecord(s, w, id))
    .on[Change.Unshare]((i, to) => i === id && to === c && ownRecord(s, w, id)) }

/** A write changes nothing it did not ask: every record the second store holds was held or is the one the write
  * adds, and every share and expiry is held in both stores or is of the share the write changes.
  */
val onlyAsked = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  t.records.forall(r => s.records.contains(r) || addsRecord(s, w, r)) &&
    t.shares.forall(sh => s.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) &&
    s.shares.forall(sh => t.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) &&
    t.expiries.forall(e => s.expiries.contains(e) || changesShare(s, w, e.record, e.to)) &&
    s.expiries.forall(e => t.expiries.contains(e) || changesShare(s, w, e.record, e.to)) }

/** Whether a share has ended by `now`, by the store's expiries. */
val ended = define { (sh: Term[Share], s: Term[CrmStore], now: Term[BigInt]) =>
  s.expiries.exists(e => e.record === sh.record && e.to === sh.to && e.until <= now) }

/** The second store is the first with exactly the shares ended by `now` removed, with their times, and the same
  * records.
  */
val endsDueAt = define { (s: Term[CrmStore], now: Term[BigInt], t: Term[CrmStore]) =>
  t.records === s.records && t.shares === s.shares.filter(sh => !ended(sh, s, now)) &&
    t.expiries === s.expiries.filter(e => !ended(make[Share](e.record, e.to), s, now)) }

/** A run of the expiry job (the code of `expire`): the shares that have not ended, and the expiries of those. */
val expireCode = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  make[CrmStore](s.records, s.shares.filter(sh => !ended(sh, s, now)),
    s.expiries.filter(e => !ended(make[Share](e.record, e.to), s, now))) }

/** The ids of the records a store holds anything about: its records, their shares and their expiries. */
val idsIn = define { (s: Term[CrmStore]) =>
  s.records.map(r => r.id) ++ s.shares.map(sh => sh.record) ++ s.expiries.map(e => e.record) }

/** What the database holds after a run of the expiry job at `now`, as the job stores it: for each record either store
  * mentions, the rows of the job's store (its code, `expireCode`) stored again where they differ.
  */
val jobDone = define { (s: Term[CrmStore], now: Term[BigInt]) =>
  (idsIn(s) ++ idsIn(expireCode(s, now))).foldLeft(s)((x, id) =>
    when(aboutRecord(s, id) =!= aboutRecord(expireCode(s, now), id))(
      replaceAbout(x, id, aboutRecord(expireCode(s, now), id))).otherwise(x)) }

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
