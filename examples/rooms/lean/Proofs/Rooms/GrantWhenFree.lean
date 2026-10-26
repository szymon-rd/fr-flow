import FrFlowGen.Rooms.GrantWhenFree.Spec

/-! A request is granted exactly when it overlaps no booking of its room (the contract). An overlap shares a
moment: the later of the two starts, which is before both ends, since each booking ends after it starts. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.GrantWhenFree.Proofs
open Rooms.GrantWhenFree

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  simp only [frflow_defs] at *
  intro held request hConsistent
  rw [h_GrantWhenNoOverlap held request hConsistent]
  have hEnds := hConsistent.1
  have hRequest := hEnds request (by simp)
  apply propext
  constructor
  · intro hNone t ht ⟨b, hb, hRoom, hbt⟩
    exact hNone ⟨b, hb, ⟨hRoom, by omega⟩, by omega⟩
  · intro hFree ⟨b, hb, ⟨hRoom, h1⟩, h2⟩
    have := hEnds b (by simp [hb])
    by_cases hLater : b.start ≤ request.start
    · exact hFree request.start ⟨by omega, by omega⟩ ⟨b, hb, hRoom, by omega, by omega⟩
    · exact hFree b.start ⟨by omega, by omega⟩ ⟨b, hb, hRoom, by omega, by omega⟩

end Rooms.GrantWhenFree.Proofs
