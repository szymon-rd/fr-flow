import FrFlowGen.Crm.Whole.Spec

/-! Crm's promises about a search hold together (owner §39): for every store the CRM holds and every clock, the
database answering with the stored records that match (today's `storedMatching`) keeps `recordsByQuery`, the
records screen then keeps `readContract`, and a user finds what the screens return (`searches`). And today's
expectation of the purpose, on one history, follows from what the CRM holds and what a search returns. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.Whole.Proofs
open Crm

theorem consistent_5 : Obl.consistent_5 := by
  intro held clock _ _
  refine ⟨fun u q r => r ∈ results (search (fun _ q => held.records.filter (fun r => decide («matches» q r))) held
    clock) (dealsOf (search (fun _ q => held.records.filter (fun r => decide («matches» q r))) held clock)) u q,
    fun _ q => held.records.filter (fun r => decide («matches» q r)), fun _ _ _ => rfl, ?_, ?_⟩
  · intro _ _ user query
    refine ⟨fun r hr => ?_, fun r hr hm => ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq] at hr
      exact hr
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hr, hm⟩
  · intro _ _ user query
    refine ⟨fun r hr => ?_, fun r hr hm => ?_⟩
    · simp only [search, List.mem_filter, decide_eq_true_eq] at hr
      exact ⟨hr.1, hr.2⟩
    · simp only [search, List.mem_filter, decide_eq_true_eq]
      exact ⟨⟨hr, hm.1⟩, hm.2⟩

theorem example_0 : Obl.example_0 := by
  intro history clock added sharedWith held expire save read deals hk ho _ _ _ _ _ _ _ hM hV _ _ hHistory
  obtain ⟨hRec, hShared⟩ := hM hk ho
  have hAsked : askedIn history = Asked.mk
      [CrmRecord.mk 1 (TenantId.mk "acme") Kind.Contact "Acme contact",
        CrmRecord.mk 2 (TenantId.mk "globex") Kind.Deal "Globex deal"]
      [Grant.mk 2 (TenantId.mk "acme") (some 100)] := by
    rw [hHistory]
    simp [askedIn, askedStep]
  simp only [hV hk ho, mayRead, hRec, hShared, sharedIn, hAsked]
  refine ⟨⟨fun hClock => ?_, fun hClock => ?_⟩, ?_⟩
  · simp [hClock, askMatches, «matches»]
  · simp [hClock, askMatches, «matches»]
  · simp [askMatches, «matches»]

end Crm.Whole.Proofs
