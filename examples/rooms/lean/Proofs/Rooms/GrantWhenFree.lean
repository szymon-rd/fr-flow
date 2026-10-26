import FrFlowGen.Rooms.GrantWhenFree.Spec

/-! The root, over moments, from the contract, over start and end times. Two bookings that end after they start
share a moment exactly when they overlap: the later of the two starts is before both ends. So a calendar whose
bookings never share a moment never overlaps (the contract applies), and a request overlaps a booking exactly when
the two share a moment (the contract's answer is the root's). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.GrantWhenFree.Proofs
open Rooms.GrantWhenFree

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  simp only [frflow_defs] at *
  intro held request ⟨hEnds, hApart⟩
  -- the moment two overlapping bookings share
  have shared : ∀ a b : Booking, a.start < a.end → b.start < b.end → a.start < b.end → b.start < a.end →
      ∃ t, (a.start ≤ t ∧ t < a.end) ∧ (b.start ≤ t ∧ t < b.end) := fun a b ha hb h1 h2 =>
    if h : a.start ≤ b.start then ⟨b.start, ⟨h, h2⟩, ⟨by omega, hb⟩⟩ else ⟨a.start, ⟨by omega, ha⟩, ⟨by omega, h1⟩⟩
  have hHeld : ∀ b ∈ held, b.start < b.end := fun b hb => hEnds b (by simp [hb])
  have hRequest := hEnds request (by simp)
  rw [h_GrantWhenNoOverlap held request ⟨hEnds, fun a ha b hb => by
    by_cases hab : a = b
    · exact Or.inl hab
    · refine Or.inr fun ⟨⟨hRoom, h1⟩, h2⟩ => ?_
      obtain ⟨t, hat, hbt⟩ := shared a b (hHeld a ha) (hHeld b hb) (by omega) (by omega)
      exact hApart a ha b hb ⟨hab, hRoom⟩ t ⟨hat, hbt⟩⟩]
  apply propext
  constructor
  · intro hNone t ht ⟨b, hb, hRoom, hbt⟩
    exact hNone ⟨b, hb, ⟨hRoom, by omega⟩, by omega⟩
  · intro hFree ⟨b, hb, ⟨hRoom, h1⟩, h2⟩
    obtain ⟨t, hbt, ht⟩ := shared b request (hHeld b hb) hRequest (by omega) (by omega)
    exact hFree t ht ⟨b, hb, hRoom, hbt⟩

end Rooms.GrantWhenFree.Proofs
