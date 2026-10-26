import FrFlowGen.Rooms.GrantWhenFree.Spec

/-! The claim, over moments, from the claim over start and end times. Two bookings that end after they start (as
every booking does) are apart exactly when they do not overlap: if they share a room and neither ends before the
other starts, the later of the two starts is a moment both cover. So the two claims give `granted` the same answer. -/

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
  intro granted h_GrantWhenNoOverlap held request hApart hHeld hRequest
  simp only [post, free]
  rw [h_GrantWhenNoOverlap held request hApart hHeld hRequest]
  exact propext (forall₂_congr fun b hb => (apart_iff_noOverlap (hHeld b hb) hRequest).symm)

end Rooms.GrantWhenFree.Proofs
