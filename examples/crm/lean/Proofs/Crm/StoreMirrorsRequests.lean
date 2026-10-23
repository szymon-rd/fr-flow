import FrFlowGen.Crm.StoreMirrorsRequests.Spec
import Proofs.Crm.Lemmas

/-! StoreMirrorsRequests from its parts, by induction over the history (`FrFlow.tracks`), as Keycloak's
sessions follow its sign-ins. Every store the CRM reaches holds the records users added, and holds a
share as current at any time exactly when what users asked shares it then. A saved write moves the
store as one more write moves what users asked: it does what was asked (WritesTakeEffect), nothing else
(WritesOnlyAsAsked), and keeps every record (RecordsKept). A run of the job ends exactly the shares
whose time has come (SharesExpire), as one more run does in what users asked: there, a record has one
share per company (`askedIn_unique`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.StoreMirrorsRequests.Proofs
open Crm Crm.Lemmas

/-- A run of the job at `now`: a share holds at `T` after it exactly when it held both at `now` and at `T`. -/
theorem job_store (s t : CrmStore) (now T id_ : Int) (c : TenantId)
    (keepsShare : Share → Bool) (hKeepsShare : ∀ sh, keepsShare sh = true ↔ ¬ ended sh s now)
    (keepsExpiry : Expiry → Bool) (hKeepsExpiry : ∀ e, keepsExpiry e = true ↔ ¬ ended (Share.mk e.record e.to) s now)
    (hShares : t.shares = s.shares.filter keepsShare) (hExpiries : t.expiries = s.expiries.filter keepsExpiry) :
    sharedNow t.shares t.expiries T id_ c ↔ sharedNow s.shares s.expiries now id_ c ∧ sharedNow s.shares s.expiries T id_ c := by
  rw [hShares, hExpiries]
  simp only [sharedNow, List.mem_filter, hKeepsShare, hKeepsExpiry, ended]
  constructor
  · rintro ⟨⟨hIn, hNotNow⟩, hNoT⟩
    refine ⟨⟨hIn, hNotNow⟩, hIn, fun ⟨e, he, hPair, hLe⟩ => hNoT ⟨e, ⟨he, ?_⟩, hPair, hLe⟩⟩
    rw [hPair.1, hPair.2]
    exact hNotNow
  · rintro ⟨⟨hIn, hNotNow⟩, _, hNoT⟩
    exact ⟨⟨hIn, hNotNow⟩, fun ⟨e, ⟨he, _⟩, hPair, hLe⟩ => hNoT ⟨e, he, hPair, hLe⟩⟩

/-- A run of the job at `now`, in what users asked: one share per record and company, so a share holds
at `T` after it exactly when it held both at `now` and at `T`. -/
theorem job_asked (gs : List Grant) (now T id_ : Int) (c : TenantId) (keeps : Grant → Bool)
    (hKeeps : ∀ g, keeps g = true ↔ ∀ t, g.until = some t → now < t)
    (hUnique : ∀ g ∈ gs, ∀ g' ∈ gs, g.record = g'.record → g.to = g'.to → g = g') :
    (∃ g ∈ gs.filter keeps, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) ↔
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → now < t) ∧
    (∃ g ∈ gs, (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) := by
  constructor
  · rintro ⟨g, hg, hPair, hKeepT⟩
    obtain ⟨hIn, hKeepNow⟩ := List.mem_filter.1 hg
    exact ⟨⟨g, hIn, hPair, (hKeeps g).1 hKeepNow⟩, ⟨g, hIn, hPair, hKeepT⟩⟩
  · rintro ⟨⟨g, hg, hPair, hKeepNow⟩, ⟨g', hg', hPair', hKeepT⟩⟩
    have hSame : g = g' := hUnique g hg g' hg' (hPair.1.trans hPair'.1.symm) (hPair.2.trans hPair'.2.symm)
    subst hSame
    exact ⟨g, List.mem_filter.2 ⟨hg, (hKeeps g).2 hKeepNow⟩, hPair, hKeepT⟩

/-- A write that changes nothing it did not ask leaves every share it does not change as it held. -/
theorem frame_store (s t : CrmStore) (w : WriteCmd) (T id_ : Int) (c : TenantId)
    (hOnly : onlyAsked s w t) (hNot : ¬ changesShare s w id_ c) :
    sharedNow t.shares t.expiries T id_ c ↔ sharedNow s.shares s.expiries T id_ c := by
  obtain ⟨⟨⟨⟨_, hSharesT⟩, hSharesS⟩, hExpiriesT⟩, hExpiriesS⟩ := hOnly
  have hShare : Share.mk id_ c ∈ t.shares ↔ Share.mk id_ c ∈ s.shares :=
    ⟨fun h => (hSharesT _ h).resolve_right hNot, fun h => (hSharesS _ h).resolve_right hNot⟩
  have hExpiry : ∀ e : Expiry, e.record = id_ → e.to = c → (e ∈ t.expiries ↔ e ∈ s.expiries) := by
    intro e hRecord hTo
    have hNotE : ¬ changesShare s w e.record e.to := by rw [hRecord, hTo]; exact hNot
    exact ⟨fun h => (hExpiriesT e h).resolve_right hNotE, fun h => (hExpiriesS e h).resolve_right hNotE⟩
  simp only [sharedNow]
  constructor
  · rintro ⟨hIn, hNo⟩
    exact ⟨hShare.1 hIn, fun ⟨e, he, hPair, hLe⟩ => hNo ⟨e, (hExpiry e hPair.1 hPair.2).2 he, hPair, hLe⟩⟩
  · rintro ⟨hIn, hNo⟩
    exact ⟨hShare.2 hIn, fun ⟨e, he, hPair, hLe⟩ => hNo ⟨e, (hExpiry e hPair.1 hPair.2).1 he, hPair, hLe⟩⟩

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  have key := FrFlow.tracks (step := fun s e => Crm.stepOf expire save s e) (init := CrmStore.mk [] [] [])
    (R := fun s es => (∀ r, r ∈ s.records ↔ r ∈ (askedIn es).records) ∧
      ∀ (id_ : Int) (c : TenantId) (T : Int), sharedNow s.shares s.expiries T id_ c ↔ sharedIn es id_ c T)
    (by
      refine ⟨fun r => ?_, fun id_ c T => ?_⟩
      · simp [askedIn]
      · simp [sharedNow, sharedIn, askedIn])
    (by
      intro s es e ⟨hRec, hShared⟩
      have hUnique := (askedIn_unique es).2
      simp only [sharedIn] at hShared ⊢
      rw [askedIn_snoc]
      generalize askedIn es = A at hRec hShared hUnique
      cases e with
      | Expired now =>
        have hJob := h_SharesExpire s now
        simp only [Crm.SharesExpire.post, Crm.endsDueAt] at hJob
        obtain ⟨⟨hRecords, hShares⟩, hExpiries⟩ := hJob
        simp only [Crm.stepOf, Crm.askedStep]
        refine ⟨fun r => by rw [hRecords]; exact hRec r, fun id_ c T => ?_⟩
        rw [job_store s (expire s now) now T id_ c _ (fun sh => by simp) _ (fun e => by simp) hShares hExpiries, hShared id_ c now, hShared id_ c T]
        exact (job_asked A.grants now T id_ c _ (fun g => by simp) hUnique).symm
      | Wrote w =>
        have hTakes := h_WritesTakeEffect s w
        have hOnly := h_WritesOnlyAsAsked s w
        have hKept := h_RecordsKept s (Event.Wrote w)
        simp only [Crm.stepOf] at hKept ⊢
        generalize Crm.afterSave save s w = t at hTakes hOnly hKept ⊢
        have hOnlyRecords := hOnly.1.1.1.1
        rcases w with ⟨a, ch⟩
        cases ch with
        | Add r =>
          simp only [Crm.askedStep]
          have hFrame : ∀ id_ c T, sharedNow t.shares t.expiries T id_ c ↔ sharedNow s.shares s.expiries T id_ c :=
            fun id_ c T => frame_store s t _ T id_ c hOnly (by simp [Crm.changesShare])
          have hAllowedIff : (r.tenant = a.tenant ∧ ¬∃ x ∈ A.records, x.id_ = r.id_) ↔
              (r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_) := by
            simp only [← hRec]
          by_cases hAllowed : r.tenant = a.tenant ∧ ¬∃ x ∈ s.records, x.id_ = r.id_
          · rw [ite_eq_left (hAllowedIff.2 hAllowed)]
            refine ⟨fun x => ?_, fun id_ c T => by rw [hFrame, hShared]⟩
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · intro hx
              rcases hOnlyRecords x hx with hs | hAdds
              · exact Or.inl ((hRec x).1 hs)
              · simp only [Crm.addsRecord] at hAdds
                exact Or.inr hAdds.1.1.symm
            · rintro (hx | rfl)
              · exact hKept x ((hRec x).2 hx)
              · simp only [Crm.takesEffect] at hTakes
                exact hTakes hAllowed
          · rw [ite_eq_right (fun h => hAllowed (hAllowedIff.1 h))]
            refine ⟨fun x => ⟨fun hx => ?_, fun hx => hKept x ((hRec x).2 hx)⟩, fun id_ c T => by rw [hFrame, hShared]⟩
            rcases hOnlyRecords x hx with hs | hAdds
            · exact (hRec x).1 hs
            · simp only [Crm.addsRecord] at hAdds
              obtain ⟨⟨hSame, hTenant⟩, hFresh⟩ := hAdds
              subst hSame
              exact absurd ⟨hTenant, hFresh⟩ hAllowed
        | ShareWith id0 to0 u =>
          have hRecT : ∀ x, x ∈ t.records ↔ x ∈ A.records := fun x =>
            ⟨fun hx => (hRec x).1 ((hOnlyRecords x hx).resolve_right (by simp [Crm.addsRecord])),
              fun hx => hKept x ((hRec x).2 hx)⟩
          simp only [Crm.askedStep]
          by_cases hAllowed : ∃ x ∈ s.records, x.id_ = id0 ∧ x.tenant = a.tenant
          · have hAllowedA : ∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
              simpa only [hRec] using hAllowed
            rw [ite_eq_left hAllowedA]
            refine ⟨hRecT, fun id_ c T => ?_⟩
            by_cases hPair : id_ = id0 ∧ c = to0
            · obtain ⟨rfl, rfl⟩ := hPair
              have hAsked : (∃ g ∈ A.grants.filter (fun g => decide (¬(g.record = id_ ∧ g.to = c))) ++ [Grant.mk id_ c u],
                  (g.record = id_ ∧ g.to = c) ∧ ∀ t, g.until = some t → T < t) ↔ ∀ t, u = some t → T < t := by
                constructor
                · rintro ⟨g, hg, hPairG, hKeep⟩
                  rcases List.mem_append.1 hg with hg | hg
                  · exact absurd ⟨g, hg, hPairG, hKeep⟩ (grant_filter_self A.grants id_ c T)
                  · rw [List.mem_singleton] at hg
                    subst hg
                    exact hKeep
                · intro hKeep
                  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ⟨rfl, rfl⟩, hKeep⟩
              rw [hAsked]
              simp only [Crm.takesEffect] at hTakes
              obtain ⟨hIn, hTimes⟩ := hTakes hAllowed
              simp only [sharedNow]
              cases u with
              | some v =>
                obtain ⟨hHas, hOnlyV⟩ := hTimes
                constructor
                · rintro ⟨_, hNo⟩ t' hSome
                  cases hSome
                  exact Int.lt_of_not_ge (fun hLe => hNo ⟨_, hHas, ⟨rfl, rfl⟩, hLe⟩)
                · intro hKeep
                  refine ⟨hIn, fun ⟨e, he, hPairE, hLe⟩ => ?_⟩
                  have hUntil := hOnlyV e he hPairE
                  have hLt := hKeep v rfl
                  rw [hUntil] at hLe
                  exact absurd hLe (Int.not_le.2 hLt)
              | none =>
                constructor
                · intro _ t' hNone
                  cases hNone
                · intro _
                  refine ⟨hIn, ?_⟩
                  rintro ⟨e, he, hPairE, _⟩
                  exact hTimes ⟨e, he, hPairE⟩
            · have hNot : ¬ changesShare s ⟨a, Change.ShareWith id0 to0 u⟩ id_ c := by
                simp only [Crm.changesShare]
                rintro ⟨⟨hRecord, hTo⟩, _⟩
                exact hPair ⟨hRecord.symm, hTo.symm⟩
              rw [frame_store s t _ T id_ c hOnly hNot, hShared, grant_append_other _ id0 to0 u T id_ c hPair,
                grant_filter_other A.grants id0 to0 T id_ c hPair]
          · have hNotA : ¬∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
              simpa only [hRec] using hAllowed
            rw [ite_eq_right hNotA]
            refine ⟨hRecT, fun id_ c T => ?_⟩
            have hNot : ¬ changesShare s ⟨a, Change.ShareWith id0 to0 u⟩ id_ c := by
              simp only [Crm.changesShare]
              rintro ⟨⟨hRecord, _⟩, hHeld⟩
              subst hRecord
              exact hAllowed hHeld
            rw [frame_store s t _ T id_ c hOnly hNot, hShared]
        | Unshare id0 to0 =>
          have hRecT : ∀ x, x ∈ t.records ↔ x ∈ A.records := fun x =>
            ⟨fun hx => (hRec x).1 ((hOnlyRecords x hx).resolve_right (by simp [Crm.addsRecord])),
              fun hx => hKept x ((hRec x).2 hx)⟩
          simp only [Crm.askedStep]
          by_cases hAllowed : ∃ x ∈ s.records, x.id_ = id0 ∧ x.tenant = a.tenant
          · have hAllowedA : ∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
              simpa only [hRec] using hAllowed
            rw [ite_eq_left hAllowedA]
            refine ⟨hRecT, fun id_ c T => ?_⟩
            by_cases hPair : id_ = id0 ∧ c = to0
            · obtain ⟨rfl, rfl⟩ := hPair
              simp only [Crm.takesEffect] at hTakes
              have hGone := hTakes hAllowed
              simp only [sharedNow]
              constructor
              · rintro ⟨hIn, _⟩
                exact absurd hIn hGone
              · intro h
                exact absurd h (grant_filter_self A.grants id_ c T)
            · have hNot : ¬ changesShare s ⟨a, Change.Unshare id0 to0⟩ id_ c := by
                simp only [Crm.changesShare]
                rintro ⟨⟨hRecord, hTo⟩, _⟩
                exact hPair ⟨hRecord.symm, hTo.symm⟩
              rw [frame_store s t _ T id_ c hOnly hNot, hShared, grant_filter_other A.grants id0 to0 T id_ c hPair]
          · have hNotA : ¬∃ x ∈ A.records, x.id_ = id0 ∧ x.tenant = a.tenant := by
              simpa only [hRec] using hAllowed
            rw [ite_eq_right hNotA]
            refine ⟨hRecT, fun id_ c T => ?_⟩
            have hNot : ¬ changesShare s ⟨a, Change.Unshare id0 to0⟩ id_ c := by
              simp only [Crm.changesShare]
              rintro ⟨⟨hRecord, _⟩, hHeld⟩
              subst hRecord
              exact hAllowed hHeld
            rw [frame_store s t _ T id_ c hOnly hNot, hShared])
  obtain ⟨hRecords, hShared⟩ := key history
  unfold Crm.StoreMirrorsRequests.claim
  exact ⟨fun r => propext (hRecords r), fun id_ c => propext (hShared id_ c clock)⟩

end Crm.StoreMirrorsRequests.Proofs
