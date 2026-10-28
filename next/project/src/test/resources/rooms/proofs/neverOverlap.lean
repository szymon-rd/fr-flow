import FrFlowGen.Rooms.neverOverlap.Spec
import Proofs.Rooms.Lemmas

/-! Every run of booking keeps the bookings stored apart: a request is added only when granted, which the calendar's
claim gives as the store's being free of it, so it is apart from every booking held. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.neverOverlap.Proofs

theorem cover_book : Obl.cover_book := by
  intro granted h _ request hr before hno hv
  rw [Lemmas.run_eq]
  have hg := Lemmas.granted_free granted h request hr before.bookingTable hno hv
  by_cases hf : free before.bookingTable request
  · have hy : granted ⟨request.room, before.bookingTable.filter (fun b => decide (b.room = request.room))⟩ request :=
      hg ▸ hf
    simp only [hy, ite_true]
    unfold neverOverlap at *
    rw [List.pairwise_append]
    refine ⟨hno, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp at hb; subst hb; exact hf a ha
  · have hn : ¬granted ⟨request.room, before.bookingTable.filter (fun b => decide (b.room = request.room))⟩ request :=
      hg ▸ hf
    simp only [hn, ite_false]; exact hno

end Rooms.neverOverlap.Proofs
