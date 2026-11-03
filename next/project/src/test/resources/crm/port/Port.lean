import FrFlowGen.Old.ReadContract.Spec
import FrFlowGen.Old.DealSearch.Spec
import FrFlowGen.Old.RecordsByQuery.Spec
import FrFlowGen.Old.SearchesMatch.Spec
import FrFlowGen.Old.Visibility.Spec
import FrFlowGen.Old.NoCrossTenantRead.Spec
import FrFlowGen.Old.StoreMirrorsRequests.Spec
import FrFlowGen.Old.SharedCrm.Spec
import FrFlowGen.Old.WriteContract.Spec
import FrFlowGen.Old.SaveWrite.Spec
import FrFlowGen.Old.WritesTakeEffect.Spec
import FrFlowGen.Old.WritesOnlyAsAsked.Spec
import FrFlowGen.Old.RecordsKept.Spec
import FrFlowGen.Old.SharesExpire.Spec
import FrFlowGen.Old.Domain.Def_saved
import FrFlowGen.Old.Domain.Term_store
import FrFlowGen.Old.Domain.Term_shares
import FrFlowGen.Old.Domain.Term_expiries
import FrFlowGen.Old.Domain.Def_runOf
import FrFlowGen.Old.Domain.Def_storedAbout
import FrFlowGen.Old.Domain.Def_expireCode
import FrFlowGen.Old.Domain.Def_afterSave
import FrFlowGen.Old.Domain.Def_stepOf
import FrFlowGen.Old.Domain.Def_results
import FrFlowGen.Old.Domain.Def_about
import FrFlowGen.Old.Domain.Def_takesEffect
import FrFlowGen.Old.Domain.Def_onlyAsked
import FrFlowGen.Old.Domain.Def_addsRecord
import FrFlowGen.Old.Domain.Def_changesShare
import FrFlowGen.Old.Domain.Def_mayRead
import FrFlowGen.Old.Domain.Def_sharedNow
import FrFlowGen.Old.Domain.Def_askMatches
import FrFlowGen.Old.Domain.Def_matches
import FrFlowGen.Crm.readContract.Spec
import FrFlowGen.Crm.dealSearch.Spec
import FrFlowGen.Crm.recordsByQuery.Spec
import FrFlowGen.Crm.searchesMatch.Spec
import FrFlowGen.Crm.visibility.Spec
import FrFlowGen.Crm.noCrossTenantRead.Spec
import FrFlowGen.Crm.storeMirrorsRequests.Spec
import FrFlowGen.Crm.sharedCrm.Spec
import FrFlowGen.Crm.writeContract.Spec
import FrFlowGen.Crm.saveWrite.Spec
import FrFlowGen.Crm.writesTakeEffect.Spec
import FrFlowGen.Crm.writesOnlyAsAsked.Spec
import FrFlowGen.Crm.recordsKept.Spec
import FrFlowGen.Crm.sharesExpire.Spec
import FrFlowGen.Crm.oneRowPerKey.Spec
import Proofs.Crm.Lemmas

/-! No statement of crm is weakened by the port (ARCHITECTURE section 9, equivalence 4): each node's claim as
today's library stated it (`reference/crm`, put in namespace `Old` over the port's types) against the port's. The
port states each in every world meeting the database's rules (`Rules`: what it holds is what its history led to, one
row per key), today's values read in it: what the CRM holds is the database's store, the history its event log, the
clock the clock model's time, and a screen's or the database's search's result its run's from the world. Of the read
side, the root and what the CRM holds, each claim is today's in every such world. Of a write and the job's store,
stated of every store, today's implies the port's of every store with one row per key, the write side's and the job's
being today's code (`saved storedAbout`, `expireCode`). Today's write side was a function of a store; the port's runs
on the database: its claim gives today's of the store the database holds, and says what it leaves too. Today's expiry
job is stated over today's world (a boundary's), and is listed, not stated here. And the seeded bugs in proven code
(section 9): code that would stand for `read` or `write`, or for the write side, is shown to break the port's claim
on a case, so Lean proves no such code. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Crm

/-- What the database's rules say of a world: what every statement of the port is stated in. -/
abbrev Rules (w : World) : Prop :=
  crmRun w.databaseModel ∧ keyedTables w.databaseModel.store ∧ oneRowPerKey w.databaseModel.store

/-- The rules, as the port's statements take them. -/
theorem in_worlds {P : World → Prop} :
    (∀ w : World, crmRun w.databaseModel → keyedTables w.databaseModel.store → oneRowPerKey w.databaseModel.store →
      P w) ↔ ∀ w, Rules w → P w :=
  ⟨fun h w ⟨h1, h2, h3⟩ => h w h1 h2 h3, fun h w h1 h2 h3 => h w ⟨h1, h2, h3⟩⟩

-- Today's defines of the domain, each the port's.

theorem matches_eq : Old.«matches» = Crm.«matches» := by
  funext q r; cases q <;> rfl

theorem askMatches_eq : Old.askMatches = Crm.askMatches := by
  funext q r; rcases q with ⟨sc, se⟩; cases sc <;> simp only [Old.askMatches, Crm.askMatches, matches_eq]

/-- Today's reader's access, over the shares and expiries; the port's, over the store holding them. -/
theorem mayRead_eq (s : CrmStore) (c : Int) : Old.mayRead s.shares s.expiries c = Crm.mayRead s c := by
  funext u r; rfl

theorem sharedNow_eq (s : CrmStore) (c : Int) : Old.sharedNow s.shares s.expiries c = fun i t => Crm.sharedNow s c i t := by
  funext i t; rfl

/-- What today's search on a screen returned, of the screens' results from a world: the port's. -/
theorem results_at (read deals : Account → Search → World → List CrmRecord × World) (w : World) (u : Account)
    (q : Ask) : Old.results (fun u q => (read u q w).1) (fun u q => (deals u q w).1) u q =
      onScreen q (read u q.search w).1 (deals u q.search w).1 := by
  rcases q with ⟨sc, se⟩; cases sc <;> rfl

theorem takesEffect_eq : Old.takesEffect = Crm.takesEffect := by
  funext s w t
  rcases w with ⟨a, ch⟩
  cases ch with
  | Add r => rfl
  | ShareWith i to u => cases u <;> simp only [Old.takesEffect, Crm.takesEffect, ownRecord]
  | Unshare i to => simp only [Old.takesEffect, Crm.takesEffect, ownRecord]

theorem addsRecord_eq : Old.addsRecord = Crm.addsRecord := by
  funext s w r; rcases w with ⟨a, ch⟩; cases ch <;> rfl

theorem changesShare_eq : Old.changesShare = Crm.changesShare := by
  funext s w i c; rcases w with ⟨a, ch⟩; cases ch <;> rfl

theorem onlyAsked_eq : Old.onlyAsked = Crm.onlyAsked := by
  funext s w t; simp only [Old.onlyAsked, Crm.onlyAsked, addsRecord_eq, changesShare_eq]

theorem about_eq : Old.about = Crm.about := by
  funext w; rcases w with ⟨_, ch⟩; cases ch <;> rfl

/-- Today's write side's code: the rows the write's code leads to about the written record. -/
def todaysSave : CrmStore → WriteCmd → CrmStore := Old.saved Old.storedAbout Crm.applyWrite

/-- What today's database held after today's write side saved a write: the port's rule's. -/
theorem afterSave_eq : Old.afterSave todaysSave = Crm.afterSave := by
  funext s w; simp only [Old.afterSave, Crm.afterSave, todaysSave, Old.saved, Old.storedAbout, about_eq]; rfl

-- What the CRM holds: today's definition, the history replayed by today's write side and job, against the port's
-- rule of the database's state, which replays the job as the database holds it after (`jobDone`).

/-- Two stores holding the same rows about every record, in the same order for each. -/
def SameRows (a b : CrmStore) : Prop := ∀ i, aboutRecord a i = aboutRecord b i

theorem expireCode_eq : Old.expireCode = Crm.expireCode := by funext s now; rfl

/-- One event on, from stores holding the same rows about every record: the port's step and today's hold the same
rows about every record too. -/
theorem step_same (a b : CrmStore) (h : SameRows a b) (e : Event) :
    SameRows (Crm.stepOf a e) (Old.stepOf Old.expireCode todaysSave b e) := by
  intro j
  cases e with
  | Wrote c =>
    simp only [Crm.stepOf, Old.stepOf, afterSave_eq, Crm.afterSave, Lemmas.about_replace]
    split
    · rename_i hj; subst hj
      rw [Runs.applyWrite_local, h (about c), ← Runs.applyWrite_local]
    · exact h j
  | Expired now =>
    simp only [Crm.stepOf, Old.stepOf, expireCode_eq]
    rw [Runs.jobDone_about, Runs.expire_local, h j, ← Runs.expire_local]

theorem fold_same : ∀ (es : List Event) (a b : CrmStore), SameRows a b →
    SameRows (es.foldl (fun s e => Crm.stepOf s e) a) (es.foldl (fun s e => Old.stepOf Old.expireCode todaysSave s e) b)
  | [], _, _, h => h
  | e :: es, a, b, h => fold_same es _ _ (step_same a b h e)

/-- What the CRM holds, of a world meeting the rules: the same rows about every record as today's definition of it,
the history replayed by today's write side and job; so the same records, shares and expiries (the job's rows stored
again may come after the others). -/
theorem crmRun (w : World) (hw : Rules w) :
    SameRows w.databaseModel.store (Old.runOf Old.expireCode todaysSave w.databaseModel.events) ∧
      (∀ r, r ∈ w.databaseModel.store.records ↔ r ∈ Old.store w.databaseModel.events Old.expireCode todaysSave) ∧
      (∀ sh, sh ∈ w.databaseModel.store.shares ↔ sh ∈ Old.shares w.databaseModel.events Old.expireCode todaysSave) ∧
      (∀ e, e ∈ w.databaseModel.store.expiries ↔
        e ∈ Old.expiries w.databaseModel.events Old.expireCode todaysSave) := by
  have h1 := hw.1
  simp only [Crm.crmRun, Crm.runOf] at h1
  have hs : SameRows w.databaseModel.store (Old.runOf Old.expireCode todaysSave w.databaseModel.events) := by
    rw [h1]; exact fold_same _ _ _ (fun _ => rfl)
  have hm := Runs.sameRows_mem _ _ (fun i _ => hs i)
  exact ⟨hs, hm.1, hm.2.1, hm.2.2⟩

-- The read side, in every world meeting the rules: today's statements of what the CRM holds and the clock then.

theorem readContract (read : Account → Search → World → List CrmRecord × World) :
    Crm.readContract.claim read ↔ ∀ w, Rules w →
      Old.ReadContract.claim w.databaseModel.store.records w.databaseModel.store.shares
        w.databaseModel.store.expiries w.clockModel (fun u q => (read u q w).1) := by
  unfold Crm.readContract.claim Old.ReadContract.claim Old.ReadContract.post
  simp only [matches_eq, mayRead_eq]
  constructor
  · intro h w hw u q
    have hr := h u q w hw.1 hw.2.1 hw.2.2
    revert hr; generalize read u q w = p; rcases p with ⟨res, aft⟩; exact id
  · intro h u q w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ u q
    revert hr; generalize read u q w = p; rcases p with ⟨res, aft⟩; exact id

theorem dealSearch (deals : Account → Search → World → List CrmRecord × World) :
    Crm.dealSearch.claim deals ↔ ∀ w, Rules w →
      Old.DealSearch.claim w.databaseModel.store.records w.databaseModel.store.shares
        w.databaseModel.store.expiries w.clockModel (fun u q => (deals u q w).1) := by
  unfold Crm.dealSearch.claim Old.DealSearch.claim Old.DealSearch.post
  simp only [matches_eq, mayRead_eq]
  constructor
  · intro h w hw u q
    have hr := h u q w hw.1 hw.2.1 hw.2.2
    revert hr; generalize deals u q w = p; rcases p with ⟨res, aft⟩; exact id
  · intro h u q w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ u q
    revert hr; generalize deals u q w = p; rcases p with ⟨res, aft⟩; exact id

theorem recordsByQuery (fetch : Account → Search → StateM Tables (List CrmRecord)) :
    Crm.recordsByQuery.claim fetch ↔ ∀ w, Rules w →
      Old.RecordsByQuery.claim w.databaseModel.store.records (fun u q => (DatabaseModel.fetch_run fetch u q w).1) := by
  unfold Crm.recordsByQuery.claim Old.RecordsByQuery.claim Old.RecordsByQuery.post
  simp only [matches_eq]
  constructor
  · intro h w hw u q
    have hr := h u q w hw.1 hw.2.1 hw.2.2
    revert hr; generalize DatabaseModel.fetch_run fetch u q w = p; rcases p with ⟨res, aft⟩; exact id
  · intro h u q w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ u q
    revert hr; generalize DatabaseModel.fetch_run fetch u q w = p; rcases p with ⟨res, aft⟩; exact id

theorem searchesMatch (read deals : Account → Search → World → List CrmRecord × World) :
    Crm.searchesMatch.claim read deals ↔ ∀ w, Rules w →
      Old.SearchesMatch.claim w.databaseModel.store.records (fun u q => (read u q w).1) (fun u q => (deals u q w).1)
        w.databaseModel.store.shares w.databaseModel.store.expiries w.clockModel := by
  unfold Crm.searchesMatch.claim Old.SearchesMatch.claim
  simp only [askMatches_eq, mayRead_eq, results_at]
  constructor
  · intro h w hw u q
    have hr := h u q w hw.1 hw.2.1 hw.2.2
    revert hr; generalize read u q.search w = p1; generalize deals u q.search w = p2
    rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id
  · intro h u q w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ u q
    revert hr; generalize read u q.search w = p1; generalize deals u q.search w = p2
    rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id

theorem visibility (read deals : Account → Search → World → List CrmRecord × World) :
    Crm.visibility.claim read deals ↔ ∀ w, Rules w →
      Old.Visibility.claim w.databaseModel.store.records (fun u q => (read u q w).1) (fun u q => (deals u q w).1)
        w.databaseModel.store.shares w.databaseModel.store.expiries w.clockModel := by
  unfold Crm.visibility.claim Old.Visibility.claim
  simp only [askMatches_eq, mayRead_eq, results_at]
  constructor
  · intro h w hw u q r
    have hr := h u q r w hw.1 hw.2.1 hw.2.2
    revert hr; generalize read u q.search w = p1; generalize deals u q.search w = p2
    rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id
  · intro h u q r w h1 h2 h3
    have hr := h w ⟨h1, h2, h3⟩ u q r
    revert hr; generalize read u q.search w = p1; generalize deals u q.search w = p2
    rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id

theorem noCrossTenantRead (read deals : Account → Search → World → List CrmRecord × World) :
    Crm.noCrossTenantRead.claim read deals ↔ ∀ w, Rules w →
      Old.NoCrossTenantRead.claim w.databaseModel.store.shares w.databaseModel.store.expiries w.clockModel
        (fun u q => (read u q w).1) (fun u q => (deals u q w).1) := by
  unfold Crm.noCrossTenantRead.claim Old.NoCrossTenantRead.claim
  simp only [Old.NoCrossTenantRead.view_ReadContract, Old.NoCrossTenantRead.view_DealSearch,
    Old.NoCrossTenantRead.rule, List.mem_map, mayRead_eq]
  constructor
  · intro h w hw
    have each : ∀ u q, (∀ r ∈ (read u q w).1, Crm.mayRead w.databaseModel.store w.clockModel u r) ∧
        ∀ r ∈ (deals u q w).1, Crm.mayRead w.databaseModel.store w.clockModel u r := by
      intro u q
      have hr := h u q w hw.1 hw.2.1 hw.2.2
      revert hr; generalize read u q w = p1; generalize deals u q w = p2
      rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id
    refine ⟨fun u q p ⟨r, hr, hp⟩ => ?_, fun u q p ⟨r, hr, hp⟩ => ?_⟩
    · subst hp; exact (each u q).1 r hr
    · subst hp; exact (each u q).2 r hr
  · intro h u q w h1 h2 h3
    have ⟨ha, hb⟩ := h w ⟨h1, h2, h3⟩
    have each : (∀ r ∈ (read u q w).1, Crm.mayRead w.databaseModel.store w.clockModel u r) ∧
        ∀ r ∈ (deals u q w).1, Crm.mayRead w.databaseModel.store w.clockModel u r :=
      ⟨fun r hr => ha u q (u, r) ⟨r, hr, rfl⟩, fun r hr => hb u q (u, r) ⟨r, hr, rfl⟩⟩
    revert each; generalize read u q w = p1; generalize deals u q w = p2
    rcases p1 with ⟨r1, a1⟩; rcases p2 with ⟨r2, a2⟩; exact id

-- What the CRM holds and the root, in every world meeting the rules.

theorem storeMirrorsRequests : Crm.storeMirrorsRequests.claim ↔ ∀ w, Rules w →
    Old.StoreMirrorsRequests.claim w.databaseModel.store.records w.databaseModel.events w.clockModel
      w.databaseModel.store.shares w.databaseModel.store.expiries :=
  ⟨fun h w hw => h w hw.1 hw.2.1 hw.2.2, fun h w h1 h2 h3 => h w ⟨h1, h2, h3⟩⟩

theorem sharedCrm (finds : Account → Ask → CrmRecord → World → Prop) (asksFor : Ask → CrmRecord → World → Prop)
    (added : TenantId → CrmRecord → World → Prop) (owner : CrmRecord → World → TenantId)
    (companyOf : Account → World → TenantId) (sharedWith : CrmRecord → TenantId → World → Prop) :
    Crm.sharedCrm.claim finds asksFor added owner companyOf sharedWith ↔ ∀ w, Rules w →
      Old.SharedCrm.claim Account Ask CrmRecord TenantId (fun u q r => finds u q r w) (fun q r => asksFor q r w)
        (fun c r => added c r w) (fun r => owner r w) (fun a => companyOf a w) (fun r c => sharedWith r c w) :=
  ⟨fun h w hw u q r => h u q r w hw.1 hw.2.1 hw.2.2, fun h u q r w h1 h2 h3 => h w ⟨h1, h2, h3⟩ u q r⟩

-- The write side and the expiry job: today's implies the port's, of every store with one row per key, the stores
-- the CRM makes and holds, today's write side and job being today's code.

theorem writeContract (write : CrmStore → WriteCmd → CrmStore) :
    Old.WriteContract.claim write → Crm.writeContract.claim write := by
  intro h s _ _ w
  have hw := h s w
  simp only [Old.WriteContract.post, takesEffect_eq, onlyAsked_eq, ne_eq] at hw
  exact hw

theorem writesTakeEffect : Old.WritesTakeEffect.claim todaysSave → Crm.writesTakeEffect.claim := by
  intro h s _ _ w
  have hw := h s w
  rw [takesEffect_eq, afterSave_eq] at hw
  exact hw

theorem writesOnlyAsAsked : Old.WritesOnlyAsAsked.claim todaysSave → Crm.writesOnlyAsAsked.claim := by
  intro h s _ _ w
  have hw := h s w
  rw [onlyAsked_eq, afterSave_eq] at hw
  exact hw

/-- A write's step is today's; a run of the job keeps the records today's job's store holds. -/
theorem recordsKept : Old.RecordsKept.claim Old.expireCode todaysSave → Crm.recordsKept.claim := by
  intro h s _ _ e r hr
  cases e with
  | Wrote w =>
    have hw := h s (Event.Wrote w) r hr
    simp only [Old.stepOf, afterSave_eq] at hw
    exact hw
  | Expired now => exact ((Runs.jobDone_mem s now).1 r).2 hr

theorem sharesExpire (expire : CrmStore → Int → CrmStore) :
    Old.SharesExpire.claim expire → Crm.sharesExpire.claim expire :=
  fun h s _ _ now => h s now

/-- The write side, of the store the database holds: today's claim of it, the port's run giving those rows. -/
theorem saveWrite (save : WriteCmd → World → CrmStore × World) (h : Crm.saveWrite.claim save) :
    ∀ w, Rules w → ∀ c, Old.SaveWrite.post Crm.applyWrite w.databaseModel.store c (save c w).1 := by
  intro w hw c
  have hs := h c w hw.1 hw.2.1 hw.2.2
  revert hs; generalize save c w = p; rcases p with ⟨res, aft⟩
  rintro ⟨-, hres⟩
  simp only [Old.SaveWrite.post, hres, about_eq, afterSave, Lemmas.about_replace, ite_true]
  rfl

-- The seeded bugs in proven code, each refuted on a case: Acme's contact and Globex's deal, nothing shared.

private def acmeContact : CrmRecord := CrmRecord.mk 1 (TenantId.mk "acme") Kind.Contact "Acme contact"
private def globexDeal : CrmRecord := CrmRecord.mk 2 (TenantId.mk "globex") Kind.Deal "Globex deal"
private def two : CrmStore := CrmStore.mk [acmeContact, globexDeal] [] []
private def ann : Account := Account.mk "ann@acme" (TenantId.mk "acme")
private def gil : Account := Account.mk "gil@globex" (TenantId.mk "globex")

/-- Ann's add and Gil's, the database holding what they led to, at time 0. -/
private def twoAdded : World := World.mk (Tables.mk two [Event.Wrote (WriteCmd.mk ann (Change.Add acmeContact)),
  Event.Wrote (WriteCmd.mk gil (Change.Add globexDeal))]) 0

private theorem two_keyed : onePerKey two := by simp [two, onePerKey, acmeContact, globexDeal]

private theorem two_rules : Rules twoAdded := by
  refine ⟨?_, two_keyed, two_keyed⟩
  simp [twoAdded, Crm.crmRun, Crm.runOf, Crm.stepOf, afterSave, applyWrite, replaceAbout, aboutRecord, about, two, ann, gil,
    acmeContact, globexDeal]

/-- Leaky read: code answering every search with every stored record shows Ann Globex's deal. -/
theorem leakyRead : ¬ Crm.readContract.claim (fun _ _ w => (w.databaseModel.store.records, w)) := by
  intro h
  have := (h ann Search.Everything twoAdded two_rules.1 two_rules.2.1 two_rules.2.2).1 globexDeal
    (by simp [twoAdded, two])
  simp [mayRead, sharedNow, twoAdded, two, ann, globexDeal] at this

/-- Relabel read: code answering with every stored record relabelled as the user's company's returns a record the
CRM does not hold. -/
theorem relabelRead : ¬ Crm.readContract.claim
    (fun u _ w => (w.databaseModel.store.records.map (fun r => { r with tenant := u.tenant }), w)) := by
  intro h
  have := (h ann Search.Everything twoAdded two_rules.1 two_rules.2.1 two_rules.2.2).1
    (CrmRecord.mk 2 (TenantId.mk "acme") Kind.Deal "Globex deal") (by simp [twoAdded, two, ann, acmeContact, globexDeal])
  simp [twoAdded, two, acmeContact, globexDeal] at this

/-- Careless write: code dropping every record not of Acme loses Globex's deal on Ann's add. -/
theorem carelessWrite :
    ¬ Crm.writeContract.claim (fun s _ => { s with records := s.records.filter (fun r => r.tenant = TenantId.mk "acme") }) := by
  intro h
  have := (h two two_keyed two_keyed (WriteCmd.mk ann (Change.Add (CrmRecord.mk 3 (TenantId.mk "acme") Kind.Deal "Acme deal")))).1.1.1
    globexDeal (by simp [two])
  simp [two, acmeContact, globexDeal] at this

/-- A seeded maker breaking one row per key: a write side handing back every record twice. Its `made_` is false, so
Lean proves none of it. -/
theorem duplicatingSave : ¬ Crm.oneRowPerKey.makes_save
    (fun _ w => ({ w.databaseModel.store with records := w.databaseModel.store.records ++ w.databaseModel.store.records }, w)) := by
  intro h
  have := h (WriteCmd.mk ann (Change.Unshare 1 (TenantId.mk "globex"))) twoAdded two_rules.1 two_rules.2.1 two_rules.2.2
  simp [twoAdded, two, oneRowPerKey, onePerKey, acmeContact, globexDeal] at this

end Port
