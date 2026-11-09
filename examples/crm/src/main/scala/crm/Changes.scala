package crm

import frflow.*

// ============================================================================
// What a write changes: the rows about one record, each kind of change, and what is asked of a store after it
// ============================================================================

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

/** Whether a write may add the record: it is of its author's company, under an id no record the store holds has. */
val freshAdd = define { (s: Term[CrmStore], w: Term[WriteCmd], r: Term[CrmRecord]) =>
  r.tenant === w.by.tenant && !s.records.exists(x => x.id === r.id) }

/** The store's shares but the one of the record with the company. */
val sharesBut = define { (s: Term[CrmStore], id: Term[BigInt], to: Term[TenantId]) =>
  s.shares.filter(sh => sh =!= make[Share](id, to)) }

/** The store's expiries but the one of the share of the record with the company. */
val expiriesBut = define { (s: Term[CrmStore], id: Term[BigInt], to: Term[TenantId]) =>
  s.expiries.filter(e => !(e.record === id && e.to === to)) }

/** The expiry a share given until a time has, or none for a share for good. */
val expiryOf = define { (id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]]) =>
  until.fold(Nil: Term[List[Expiry]])(u => make[Expiry](id, to, u) :: (Nil: Term[List[Expiry]])) }

/** An add: the record added, when the write may add it. */
val addRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], r: Term[CrmRecord]) =>
  when(freshAdd(s, w, r))(make[CrmStore](s.records :+ r, s.shares, s.expiries)).otherwise(s) }

/** A share: the share made, with its time, when the record is of the author's company. */
val shareRecord = define {
  (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]]) =>
    when(ownRecord(s, w, id))(make[CrmStore](s.records, sharesBut(s, id, to) :+ make[Share](id, to),
      expiriesBut(s, id, to) ++ expiryOf(id, to, until))).otherwise(s) }

/** An unshare: the share gone, with its time, when the record is of the author's company. */
val unshareRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId]) =>
  when(ownRecord(s, w, id))(make[CrmStore](s.records, sharesBut(s, id, to), expiriesBut(s, id, to))).otherwise(s) }

/** A write (the code of `write`): its change, made when its author's company may make it. */
val applyWrite = define { (s: Term[CrmStore], w: Term[WriteCmd]) =>
  w.change
    .on[Change.Add](r => addRecord(s, w, r))
    .on[Change.ShareWith]((id, to, until) => shareRecord(s, w, id, to, until))
    .on[Change.Unshare]((id, to) => unshareRecord(s, w, id, to)) }

/** The store with the written record's rows replaced by those the write leads to. */
val afterSave = define { (s: Term[CrmStore], w: Term[WriteCmd]) =>
  val id = about(w)
  replaceAbout(s, id, aboutRecord(applyWrite(s, w), id)) }

// ============================================================================
// What a write asks of the store after it
// ============================================================================

/** Whether the store holds no time for the share of the record with the company. */
val noTimeFor = define { (t: Term[CrmStore], id: Term[BigInt], to: Term[TenantId]) =>
  !t.expiries.exists(e => e.record === id && e.to === to) }

/** Whether the store's only time for the share of the record with the company is `u`. */
val onlyTime = define { (t: Term[CrmStore], id: Term[BigInt], to: Term[TenantId], u: Term[BigInt]) =>
  t.expiries.contains(make[Expiry](id, to, u)) &&
    t.expiries.forall(e => (e.record === id && e.to === to) implies (e.until === u)) }

/** Whether the store's time for the share is the one given: none for a share for good. */
val shareTimeIs = define { (t: Term[CrmStore], id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]]) =>
  until.fold(noTimeFor(t, id, to))(u => onlyTime(t, id, to, u)) }

/** Whether the store holds the share of the record with the company, with the time given. */
val sharedUntil = define { (t: Term[CrmStore], id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]]) =>
  t.shares.contains(make[Share](id, to)) && shareTimeIs(t, id, to, until) }

/** Whether an add the write may make left the record in the second store. */
val addTakes = define { (s: Term[CrmStore], w: Term[WriteCmd], r: Term[CrmRecord], t: Term[CrmStore]) =>
  freshAdd(s, w, r) implies t.records.contains(r) }

/** Whether a share of the author's company's record left it shared, with its time, in the second store. */
val shareTakes = define {
  (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId], until: Term[Option[BigInt]],
      t: Term[CrmStore]) =>
    ownRecord(s, w, id) implies sharedUntil(t, id, to, until) }

/** Whether an unshare of the author's company's record left it unshared in the second store. */
val unshareTakes = define {
  (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], to: Term[TenantId], t: Term[CrmStore]) =>
    ownRecord(s, w, id) implies !t.shares.contains(make[Share](id, to)) }

/** Whether the second store holds what a write asks, as far as its author's company may ask it. */
val takesEffect = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  w.change
    .on[Change.Add](r => addTakes(s, w, r, t))
    .on[Change.ShareWith]((id, to, until) => shareTakes(s, w, id, to, until, t))
    .on[Change.Unshare]((id, to) => unshareTakes(s, w, id, to, t)) }

/** Whether the second store holds every record the first holds. */
val keepsRecords = define { (s: Term[CrmStore], t: Term[CrmStore]) => s.records.forall(r => t.records.contains(r)) }

/** The records a store holds of companies other than the one given. */
val othersRecords = define { (s: Term[CrmStore], c: Term[TenantId]) => s.records.filter(r => r.tenant =!= c) }

/** Whether the second store holds the records of companies other than the write's author's as the first does. */
val othersKept = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  othersRecords(t, w.by.tenant) === othersRecords(s, w.by.tenant) }

/** Whether a write adds the record: it asks to add it, and may. */
val addsRecord = define { (s: Term[CrmStore], w: Term[WriteCmd], r: Term[CrmRecord]) =>
  w.change
    .on[Change.Add](x => x === r && freshAdd(s, w, r))
    .on[Change.ShareWith]((_, _, _) => False)
    .on[Change.Unshare]((_, _) => False) }

/** Whether a write changes the share of the record with that id with the company: it shares or unshares it, of a
  * record of its author's company.
  */
val changesShare = define { (s: Term[CrmStore], w: Term[WriteCmd], id: Term[BigInt], c: Term[TenantId]) =>
  w.change
    .on[Change.Add](_ => False)
    .on[Change.ShareWith]((i, to, _) => i === id && to === c && ownRecord(s, w, id))
    .on[Change.Unshare]((i, to) => i === id && to === c && ownRecord(s, w, id)) }

/** Whether every record the second store holds was held in the first or is the one the write adds. */
val recordsOnlyAdded = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  t.records.forall(r => s.records.contains(r) || addsRecord(s, w, r)) }

/** Whether the two stores' shares differ only in the share the write changes. */
val sharesOnlyChanged = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  t.shares.forall(sh => s.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) &&
    s.shares.forall(sh => t.shares.contains(sh) || changesShare(s, w, sh.record, sh.to)) }

/** Whether the two stores' times differ only in the time of the share the write changes. */
val expiriesOnlyChanged = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  t.expiries.forall(e => s.expiries.contains(e) || changesShare(s, w, e.record, e.to)) &&
    s.expiries.forall(e => t.expiries.contains(e) || changesShare(s, w, e.record, e.to)) }

/** Whether the second store differs from the first only in what the write asks. */
val onlyAsked = define { (s: Term[CrmStore], w: Term[WriteCmd], t: Term[CrmStore]) =>
  recordsOnlyAdded(s, w, t) &&
    sharesOnlyChanged(s, w, t) &&
    expiriesOnlyChanged(s, w, t) }
