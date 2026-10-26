import FrFlowGen.Rooms.GrantWhenFree.Spec

/-! The root, over moments, from the contract, over start and end times. Two bookings that end after they start
are apart exactly when they do not overlap: if they share a room and neither ends before the other starts, the later
of the two starts is a moment both cover. So the claim's precondition gives the contract's, and the answers agree. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Rooms.GrantWhenFree.Proofs
open Rooms.GrantWhenFree

theorem apart_iff_noOverlap {a b : Booking} (ha : endsAfterStart a) (hb : endsAfterStart b) :
    apart a b ↔ noOverlap a b := by
  simp only [apart, noOverlap, covers, endsAfterStart] at *
  constructor
  · rintro (h | h)
    · exact .inl (.inl h)
    · have := h (max a.start b.start); omega
  · rintro ((h | h) | h)
    · exact .inl h
    all_goals exact .inr fun t => by omega

theorem complete : Obl.complete := by
  unfold Obl.complete
  frflow_intro
  simp only [claim, GrantWhenNoOverlap.claim, GrantWhenNoOverlap.post] at *
  intro held request ⟨hEnds, hApart⟩
  have key {a b : Booking} (ha : a ∈ request :: held) (hb : b ∈ request :: held) :=
    apart_iff_noOverlap (hEnds a ha) (hEnds b hb)
  rw [h_GrantWhenNoOverlap held request ⟨hEnds, hApart.imp_of_mem fun ha hb => (key (.tail _ ha) (.tail _ hb)).1⟩]
  exact propext (forall₂_congr fun b hb => (key (.tail _ hb) (.head _)).symm)

end Rooms.GrantWhenFree.Proofs
