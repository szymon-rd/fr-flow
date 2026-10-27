package crm

import examples.Folds.*
import frflow.*

/** Whether a record is one a search asks for. */
val matches = define { (q: Term[Search], r: Term[CrmRecord]) =>
  q.on[Search.ById](id => r.id === id)
    .on[Search.OfKind](k => r.kind === k)
    .on(Search.Everything)(True) }

/** Whether the CRM holds a share of the record with that id with the company now, and the share's time, if it was
  * given until one, has not come by the clock.
  */
val sharedNow = define { (id: Term[BigInt], c: Term[TenantId]) =>
  held.shares.contains(make[Share](id, c)) && !held.expiries.exists(e => e.record === id && e.to === c && e.until <= clock) }

/** Whether a reader may see a record: it is their company's, or shared with it now. */
val mayRead = define { (reader: Term[Account], r: Term[CrmRecord]) =>
  r.tenant === reader.tenant || sharedNow(r.id, reader.tenant) }

/** Whether a record is one a search on a screen asks for: the sales screen asks for deals only. */
val askMatches = define { (q: Term[Ask], r: Term[CrmRecord]) =>
  q.screen.on[Screen.Records.type](matches(q.search, r))
    .on(Screen.Sales)(r.kind === (Kind.Deal: Kind) && matches(q.search, r)) }

/** What a search on a screen returns: the records screen's, or the sales screen's. */
val results = define { (u: Term[Account], q: Term[Ask]) =>
  q.screen.on[Screen.Records.type](read(u, q.search)).on(Screen.Sales)(deals(u, q.search)) }

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

/** What the database holds after the write side saves a write: what it held, with the rows about the written record
  * replaced by those it stored.
  */
val afterSave = define { (s: Term[CrmStore], w: Term[WriteCmd]) => replaceAbout(s, about(w), save(s, w)) }

/** Whether the store holds a record of that id of the write's author's company. */
val ownRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt]) =>
  s.records.exists(x => x.id === id && x.tenant === w.by.tenant) }

/** What a write asks, as far as its author's company may ask it: an Add of a record of their company with a fresh id
  * stores it; a share of a record of their company is made, until the time given (its only time) or for good (with
  * no time); an unshare removes it.
  */
val takesEffect = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  w.change
    .on[Change.Add](r => (r.tenant === w.by.tenant && !s.records.exists(x => x.id === r.id)) implies t.records.contains(r))
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

/** One event: a write, saved by the write side, or a run of the expiry job. */
val stepOf = define { (s: Term[CrmStore], e: Term[Event]) =>
  e.on[Event.Wrote](w => afterSave(s, w)).on[Event.Expired](now => expire(s, now)) }

/** The store a history of events leads to, from the empty store the CRM starts with. */
val runOf = define { (es: Term[List[Event]]) =>
  es.foldLeft(make[CrmStore](Nil: Term[List[CrmRecord]], Nil: Term[List[Share]], Nil: Term[List[Expiry]]))(
    (s, e) => stepOf(s, e)) }
