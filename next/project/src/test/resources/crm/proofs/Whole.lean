import FrFlowGen.Crm.Whole.Spec
import Proofs.Crm.Lemmas

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

/-- What the CRM holds, the history replayed by the write side's and the job's code over a store answering from the
rows it is given (today's `storedAbout`), holds one row per key: so it is what the history led to (`crmRun`), the
write side saves as `saveWrite` says, and the store stores as `storeEdits` says. -/
theorem consistent_6 : Obl.consistent_6 := by
  intro history
  have keyed : onePerKey (runOf expireCode (saved (fun id_ t => aboutRecord t id_) applyWrite) history) := by
    unfold runOf
    refine FrFlow.always _ (fun s => onePerKey s) _ (by simp [onePerKey]) (fun s e hs => ?_) history
    cases e with
    | Wrote w =>
      exact Lemmas.replace_onePerKey s _ (about w) hs
        (Lemmas.aboutRecord_onePerKey _ _ (Lemmas.applyWrite_onePerKey s w hs))
    | Expired now => exact Lemmas.endsDueAt_onePerKey s now (expireCode s now) ⟨⟨rfl, rfl⟩, rfl⟩ hs
  exact ⟨_, _, keyed, keyed, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

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
