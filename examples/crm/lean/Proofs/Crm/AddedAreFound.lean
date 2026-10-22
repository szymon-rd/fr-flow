import FrFlowGen.Crm.AddedAreFound.Spec

/-! AddedAreFound from its parts: the history is the events before the add, the add, and the events
after it. Right after the add the CRM holds the record (WritesTakeEffect); no later event removes it
(RecordsKept, by induction over the events after it: `FrFlow.always`); so the CRM holds it now, and a
search of its author's that asks for it returns it (Visibility: it is their company's). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.AddedAreFound.Proofs
open Crm.AddedAreFound

theorem complete : Obl.complete := by
  unfold Obl.complete
  intro history expire save read deals clock hVis hTake hKept
  simp only [Crm.AddedAreFound.claim, Crm.Visibility.claim, Crm.WritesTakeEffect.claim, Crm.RecordsKept.claim] at *
  intro u r hAdded q hq
  obtain ⟨hten, pre, post, hh, hfresh⟩ := hAdded
  -- Right after the add, the CRM holds the record.
  have h0 : r ∈ (Crm.stepOf expire save (Crm.runOf expire save pre) (Event.Wrote (WriteCmd.mk u (Change.Add r)))).records := by
    have := hTake (Crm.runOf expire save pre) (WriteCmd.mk u (Change.Add r))
    simp only [Crm.takesEffect] at this
    simp only [Crm.stepOf]
    exact this ⟨hten, hfresh⟩
  -- No event after it removes it.
  have hnow : r ∈ (Crm.runOf expire save history).records := by
    rw [hh]
    simp only [Crm.runOf, List.foldl_append, List.foldl_cons]
    exact FrFlow.always (fun s e => Crm.stepOf expire save s e) (fun s => r ∈ s.records) _ h0
      (fun s e hs => hKept s e r hs) post
  have hv := hVis u q r
  rw [hv]
  refine ⟨⟨hnow, hq⟩, ?_⟩
  simp only [Crm.mayRead]
  exact Or.inl hten

end Crm.AddedAreFound.Proofs
