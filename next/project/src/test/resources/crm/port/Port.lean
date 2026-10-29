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
import FrFlowGen.Old.StoreEdits.Spec
import FrFlowGen.Old.WritesTakeEffect.Spec
import FrFlowGen.Old.WritesOnlyAsAsked.Spec
import FrFlowGen.Old.RecordsKept.Spec
import FrFlowGen.Old.SharesExpire.Spec
import FrFlowGen.Old.Domain.Term_store
import FrFlowGen.Old.Domain.Term_shares
import FrFlowGen.Old.Domain.Term_expiries
import FrFlowGen.Crm.readContract.Spec
import FrFlowGen.Crm.dealSearch.Spec
import FrFlowGen.Crm.recordsByQuery.Spec
import FrFlowGen.Crm.searchesMatch.Spec
import FrFlowGen.Crm.visibility.Spec
import FrFlowGen.Crm.noCrossTenantRead.Spec
import FrFlowGen.Crm.storeMirrorsRequests.Spec
import FrFlowGen.Crm.sharedCrm.Spec
import FrFlowGen.Crm.crmRun.Spec
import FrFlowGen.Crm.writeContract.Spec
import FrFlowGen.Crm.saveWrite.Spec
import FrFlowGen.Crm.storeEdits.Spec
import FrFlowGen.Crm.writesTakeEffect.Spec
import FrFlowGen.Crm.writesOnlyAsAsked.Spec
import FrFlowGen.Crm.recordsKept.Spec
import FrFlowGen.Crm.sharesExpire.Spec
import FrFlowGen.Crm.oneRowPerKey.Spec

/-! Crm's statements as today's library stated them (`reference/crm`, in namespace `Old` over the port's types),
against the port's (ARCHITECTURE section 9, equivalence 4). Today's store, shares and expiries were defines of the
history replayed; the port's are the fields of what the CRM holds, which `crmRun` says is the history replayed. The
tables hold one row per key (owner §40): each statement about what the CRM holds is today's for a store holding one
row per key, as the stores the CRM holds do (`keyedTables`); each about every store (a write, a run of the expiry
job, the database's store) is today's for every store holding one row per key, and today's implies it. Today's
expiry job is stated over today's world (a boundary's), and is listed, not stated here. And the seeded bugs in
proven code (section 9): code that would stand for `read` or `write` is shown to break the port's claim on a case,
so Lean proves no such code. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Crm

-- Today's defines of the domain, each the port's.

theorem matches_eq : Old.«matches» = Crm.«matches» := by
  funext q r; cases q <;> rfl

theorem askMatches_eq : Old.askMatches = Crm.askMatches := by
  funext q r; rcases q with ⟨sc, se⟩; cases sc <;> simp only [Old.askMatches, Crm.askMatches, matches_eq]

theorem results_eq : Old.results = Crm.results := by
  funext read deals u q; rcases q with ⟨sc, se⟩; cases sc <;> rfl

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

/-- What a save returns holds only the rows about the written record (as `saveWrite` says of the write side). -/
def onlyRows (save : CrmStore → WriteCmd → CrmStore) : Prop := ∀ s w, aboutRecord (save s w) (about w) = save s w

/-- Today's database after a save held what the save returned; the port's holds its rows about the written record,
as the database's `storeAbout` does: the same, of a save returning only those. -/
theorem about_eq : Old.about = Crm.about := by
  funext w; rcases w with ⟨_, ch⟩; cases ch <;> rfl

theorem replaceAbout_eq : Old.replaceAbout = Crm.replaceAbout := by
  funext s i r; rfl

theorem afterSave_eq (save) (h : onlyRows save) : Old.afterSave save = Crm.afterSave save := by
  funext s w; simp only [Old.afterSave, Crm.afterSave, h s w, about_eq, replaceAbout_eq]

theorem stepOf_eq (expire save) (h : onlyRows save) : Old.stepOf expire save = Crm.stepOf expire save := by
  funext s e; cases e with
  | Wrote w => simp only [Old.stepOf, Crm.stepOf, afterSave_eq save h]
  | Expired now => rfl

theorem runOf_eq (expire save) (h : onlyRows save) : Old.runOf expire save = Crm.runOf expire save := by
  funext es; simp only [Old.runOf, Crm.runOf, stepOf_eq expire save h]

-- What the CRM holds: what the history led to (`crmRun`), today's store, shares and expiries.

theorem crmRun (held history expire save) (hk : onePerKey held) (hs : onlyRows save)
    (h : Crm.crmRun.claim held history expire save) :
    held.records = Old.store history expire save ∧ held.shares = Old.shares history expire save ∧
      held.expiries = Old.expiries history expire save := by
  have e := h hk hk
  simp only [Old.store, Old.shares, Old.expiries, runOf_eq expire save hs]
  rw [← e]
  exact ⟨rfl, rfl, rfl⟩

-- The read side, of a store holding one row per key: today's statements.

theorem readContract (read held clock) (hk : onePerKey held) :
    Old.ReadContract.claim held.records held.shares held.expiries clock read ↔
      Crm.readContract.claim read held clock := by
  unfold Old.ReadContract.claim Old.ReadContract.post Crm.readContract.claim
  rw [matches_eq]
  exact ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem dealSearch (deals held clock) (hk : onePerKey held) :
    Old.DealSearch.claim held.records held.shares held.expiries clock deals ↔
      Crm.dealSearch.claim deals held clock := by
  unfold Old.DealSearch.claim Old.DealSearch.post Crm.dealSearch.claim
  rw [matches_eq]
  exact ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem recordsByQuery (fetch held) (hk : onePerKey held) :
    Old.RecordsByQuery.claim held.records fetch ↔ Crm.recordsByQuery.claim fetch held := by
  unfold Old.RecordsByQuery.claim Old.RecordsByQuery.post Crm.recordsByQuery.claim
  rw [matches_eq]
  exact ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem searchesMatch (read deals held clock) (hk : onePerKey held) :
    Old.SearchesMatch.claim held.records read deals held.shares held.expiries clock ↔
      Crm.searchesMatch.claim held read deals clock := by
  unfold Old.SearchesMatch.claim Crm.searchesMatch.claim
  rw [askMatches_eq, results_eq]
  exact ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem visibility (read deals held clock) (hk : onePerKey held) :
    Old.Visibility.claim held.records read deals held.shares held.expiries clock ↔
      Crm.visibility.claim held read deals clock := by
  unfold Old.Visibility.claim Crm.visibility.claim
  rw [askMatches_eq, results_eq]
  exact ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem noCrossTenantRead (read deals held clock) (hk : onePerKey held) :
    Old.NoCrossTenantRead.claim held.shares held.expiries clock read deals ↔
      Crm.noCrossTenantRead.claim read deals held clock := by
  unfold Old.NoCrossTenantRead.claim Crm.noCrossTenantRead.claim
  simp only [Old.NoCrossTenantRead.view_ReadContract, Old.NoCrossTenantRead.view_DealSearch,
    Old.NoCrossTenantRead.rule, List.mem_map]
  constructor
  · intro h _ _ u q
    exact ⟨fun r hr => h.1 u q (u, r) ⟨r, hr, rfl⟩, fun r hr => h.2 u q (u, r) ⟨r, hr, rfl⟩⟩
  · intro h
    refine ⟨fun u q p ⟨r, hr, hp⟩ => ?_, fun u q p ⟨r, hr, hp⟩ => ?_⟩
    · subst hp; exact (h hk hk u q).1 r hr
    · subst hp; exact (h hk hk u q).2 r hr

theorem storeMirrorsRequests (held history clock) (hk : onePerKey held) :
    Old.StoreMirrorsRequests.claim held.records history clock held.shares held.expiries ↔
      Crm.storeMirrorsRequests.claim held history clock :=
  ⟨fun h _ _ => h, fun h => h hk hk⟩

theorem sharedCrm (finds asksFor added owner companyOf sharedWith) :
    Old.SharedCrm.claim Account Ask CrmRecord TenantId finds asksFor added owner companyOf sharedWith ↔
      Crm.sharedCrm.claim finds asksFor added owner companyOf sharedWith := Iff.rfl

-- The write side and the expiry job, of every store: today's implies the port's, of every store with one row per
-- key, the stores the CRM makes and holds.

theorem writeContract (write) : Old.WriteContract.claim write → Crm.writeContract.claim write := by
  intro h s _ _ w
  have hw := h s w
  simp only [Old.WriteContract.post, takesEffect_eq, onlyAsked_eq, ne_eq] at hw
  exact hw

theorem saveWrite (write save) : Old.SaveWrite.claim write save → Crm.saveWrite.claim save write :=
  fun h s _ _ w => h s w

theorem storeEdits (storeRows) : Old.StoreEdits.claim storeRows → Crm.storeEdits.claim storeRows :=
  fun h id_ t _ _ => h id_ t

theorem writesTakeEffect (save) (hs : onlyRows save) :
    Old.WritesTakeEffect.claim save → Crm.writesTakeEffect.claim save := by
  intro h s _ _ w
  have hw := h s w
  rw [takesEffect_eq, afterSave_eq save hs] at hw
  exact hw

theorem writesOnlyAsAsked (save) (hs : onlyRows save) :
    Old.WritesOnlyAsAsked.claim save → Crm.writesOnlyAsAsked.claim save := by
  intro h s _ _ w
  have hw := h s w
  rw [onlyAsked_eq, afterSave_eq save hs] at hw
  exact hw

theorem recordsKept (expire save) (hs : onlyRows save) :
    Old.RecordsKept.claim expire save → Crm.recordsKept.claim expire save := by
  intro h s _ _ e
  have hw := h s e
  rw [stepOf_eq expire save hs] at hw
  exact hw

theorem sharesExpire (expire) : Old.SharesExpire.claim expire → Crm.sharesExpire.claim expire :=
  fun h s _ _ now => h s now

-- The seeded bugs in proven code, each refuted on a case: Acme's contact and Globex's deal, nothing shared.

private def acmeContact : CrmRecord := CrmRecord.mk 1 (TenantId.mk "acme") Kind.Contact "Acme contact"
private def globexDeal : CrmRecord := CrmRecord.mk 2 (TenantId.mk "globex") Kind.Deal "Globex deal"
private def two : CrmStore := CrmStore.mk [acmeContact, globexDeal] [] []
private def ann : Account := Account.mk "ann@acme" (TenantId.mk "acme")

private theorem two_keyed : onePerKey two := by simp [two, onePerKey, acmeContact, globexDeal]

/-- Leaky read: code answering every search with every stored record shows Ann Globex's deal. -/
theorem leakyRead : ¬ Crm.readContract.claim (fun _ _ => two.records) two 0 := by
  intro h
  have := (h two_keyed two_keyed ann Search.Everything).1 globexDeal (by simp [two])
  simp [mayRead, sharedNow, two, ann, globexDeal] at this

/-- Relabel read: code answering with every stored record relabelled as the user's company's returns a record the
CRM does not hold. -/
theorem relabelRead :
    ¬ Crm.readContract.claim (fun u _ => two.records.map (fun r => { r with tenant := u.tenant })) two 0 := by
  intro h
  have := (h two_keyed two_keyed ann Search.Everything).1 (CrmRecord.mk 2 (TenantId.mk "acme") Kind.Deal "Globex deal")
    (by simp [two, ann, acmeContact, globexDeal])
  simp [two, acmeContact, globexDeal] at this

/-- Careless write: code dropping every record not of Acme loses Globex's deal on Ann's add. -/
theorem carelessWrite :
    ¬ Crm.writeContract.claim (fun s _ => { s with records := s.records.filter (fun r => r.tenant = TenantId.mk "acme") }) := by
  intro h
  have := (h two two_keyed two_keyed (WriteCmd.mk ann (Change.Add (CrmRecord.mk 3 (TenantId.mk "acme") Kind.Deal "Acme deal")))).1.1.1
    globexDeal (by simp [two])
  simp [two, acmeContact, globexDeal] at this

/-- A seeded maker breaking one row per key: a write side handing back every record twice. Its `made_` is false, so
Lean proves none of it, and the step taking it (`storeMirrorsRequests`, step 12 ruling) rests on it unproven. -/
theorem duplicatingSave : ¬ Crm.oneRowPerKey.makes_save (fun s _ => { s with records := s.records ++ s.records }) := by
  intro h
  have := h two two_keyed two_keyed (WriteCmd.mk ann (Change.Unshare 1 (TenantId.mk "globex")))
  simp [two, oneRowPerKey, onePerKey, acmeContact, globexDeal] at this

end Port
