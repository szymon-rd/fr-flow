import FrFlowGen.Crm.SharedCrm.Spec

/-! The root from its parts, and its expectations. Finding is Visibility in the root's terms, of what the
history led to (CrmRun); an added record found is AddedAreFound; what a write does, and leaves alone, is
WritesTakeEffect and WritesInCompany, the run of a history and one more write being that write saved on
the run of the history (`List.foldl_append`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.SharedCrm.Proofs
open Crm.SharedCrm

/-- The run of a history and then one more write: that write saved on the run of the history. -/
theorem runOf_wrote (expire : Crm.CrmStore → Int → Crm.CrmStore) (save : Crm.CrmStore → Crm.WriteCmd → Crm.CrmStore)
    (es : List Crm.Event) (w : Crm.WriteCmd) :
    Crm.runOf expire save (es ++ [Crm.Event.Wrote w]) = Crm.afterSave save (Crm.runOf expire save es) w := by
  simp only [Crm.runOf, List.foldl_append, List.foldl_cons, List.foldl_nil, Crm.stepOf]

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro read deals history expire save clock hAdd hVis hTake hComp
  simp only [Crm.SharedCrm.claim, Crm.AddedAreFound.claim, Crm.Visibility.claim, Crm.WritesTakeEffect.claim,
    Crm.WritesInCompany.claim] at *
  refine ⟨⟨⟨fun u q r => ?_, ?_⟩, fun es w => ?_⟩, fun es w c hc => ?_⟩
  · simpa only [Crm.finds, Crm.stored, Crm.asksFor, Crm.owner, Crm.companyOf, Crm.sharedWith, Crm.store, Crm.mayRead]
      using hVis u q r
  · simpa only [Crm.added, Crm.asksFor, Crm.finds] using hAdd
  · rw [runOf_wrote]
    exact hTake _ w
  · rw [runOf_wrote]
    exact hComp es w c hc

theorem expect_0 : Obl.expect_0 := by
  unfold Obl.expect_0
  intro read deals history expire save clock h
  simp only [Crm.SharedCrm.claim, Crm.SharedCrm.expected_0] at *
  have h1 := h.1.1.1
  simp only [Crm.finds, Crm.stored, Crm.asksFor, Crm.owner, Crm.companyOf, Crm.sharedWith, Crm.sharedNow,
    Crm.shares, Crm.expiries] at h1
  intro hrun
  simp only [hrun] at h1
  refine ⟨⟨fun hc => ?_, fun hc => ?_⟩, ?_⟩
  · subst hc
    refine ⟨?_, ?_⟩ <;> (rw [h1]; simp [Crm.askMatches, Crm.matches])
  · subst hc
    refine ⟨?_, ?_⟩
    · rw [h1]; simp [Crm.askMatches, Crm.matches]
    · rw [h1]; simp [Crm.askMatches, Crm.matches]
  · rw [h1]; simp [Crm.askMatches, Crm.matches]

theorem expect_1 : Obl.expect_1 := by
  unfold Obl.expect_1
  intro read deals history expire save clock h
  simp only [Crm.SharedCrm.claim, Crm.SharedCrm.expected_1] at *
  intro hh
  have h2 := h.1.1.2
  simp only [Crm.added, Crm.asksFor, Crm.finds, Crm.addedIn] at h2
  refine h2 _ _ ⟨rfl, [], [], by simp [hh], by simp [Crm.runOf]⟩ _ ?_
  simp [Crm.askMatches, Crm.matches]

end Crm.SharedCrm.Proofs
